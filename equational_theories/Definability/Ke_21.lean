import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4535`: `x ◇ (y ◇ z) = (y ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_y_pyy_pxy_Equation4535 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4535 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4535.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
        intro X0 X1 X2 X3
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
      have b0e31 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ y) (σ y) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y y X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op X0 X2) = (k X3 (M.op X0 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 X3 (M.op X0 X2)
           have i₂ := b0e11 (M.op X0 X2) X0 X2 X1
           grind)
        | (have i₁ := b0e14 X0 (M.op X1 X3)
           have i₂ := b0e11 (M.op X1 X3) X1 X2 X3
           grind)
        | exact superpose b0e11 b0e14
        | (have j0 := b0e14 X3 (M.op X0 X2)
           grind)
        | exact resolve b0e14 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e32 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X0 X2 y
           have i₂ := b0e43 X0
           grind)
        | (have i₁ := b0e11 X0 y X2 X0
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e11
        | exact resolve b0e11 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X0 y X2
           have i₂ := b0e43 X0
           grind)
        | (have i₁ := b0e11 X0 y X0 x
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e11
        | exact resolve b0e11 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e71 X0 X1 X2
           have i₂ := b0e38 X1 X0
           grind)
        | exact superpose b0e38 b0e71
        | exact resolve b0e71 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e71
      have b0e81 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e70 X0 X1 X2
           have i₂ := b0e32 X1 X0
           grind)
        | exact superpose b0e32 b0e70
        | exact resolve b0e70 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e70
      have b0e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X1)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e91 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X2 X0
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e16 X2 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e95 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X0 X1) X0 X2 X1
           have i₂ := b0e16 X3 (M.op X0 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X3 (M.op X0 X1)
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e97 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e91 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91
      have b0e99 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) y) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e95 X0 X1 x X3
           have i₂ := b0e81 X0 (M.op X0 X1) x
           grind)
        | exact superpose b0e81 b0e95
        | (have j0 := b0e95 X0 X1 x X3
           grind)
        | exact resolve b0e95 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95
      have b0e107 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y (M.op X0 X1)) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e99 X0 X1 X3
           have i₂ := b0e43 (M.op X0 X1)
           grind)
        | exact superpose b0e43 b0e99
        | (have j0 := b0e99 X0 X1 X3
           grind)
        | exact resolve b0e99 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99
      have b0e113 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y y) ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e107 X0 X1 X3
           have i₂ := b0e81 X0 y X1
           grind)
        | exact superpose b0e81 b0e107
        | (have j0 := b0e107 X0 X1 X3
           grind)
        | exact resolve b0e107 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107
      have b0e119 : ∀ X0 X1 X3 : G, (M.op X0 X1) = y ∨ (k X3 (M.op X0 X1)) = (M.op X3 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e113 X0 X1 X3
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e113
        | (have j0 := b0e113 X0 X1 X3
           grind)
        | exact resolve b0e113 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113
      have b0e125 : ∀ X0 X1 X3 : G, (k X3 (M.op X0 X1)) = (M.op X3 y) ∨ (M.op X0 X1) = y ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e119 X0 X1 X3
           have i₂ := b0e81 X0 X3 X1
           grind)
        | exact superpose b0e81 b0e119
        | (have j0 := b0e119 X0 X1 X3
           grind)
        | exact resolve b0e119 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e119
      have b0e130 : ∀ X0 X1 X3 : G, (k X3 (M.op X0 X1)) = (M.op X3 y) ∨ (M.op X0 X1) = (M.op y X3) ∨ (M.op X0 X1) = y := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e125 X0 X1 X3
           have i₂ := b0e80 X0 X3 X1
           grind)
        | exact superpose b0e80 b0e125
        | (have j0 := b0e125 X0 X1 X3
           grind)
        | exact resolve b0e125 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125
      have b0e221 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e229 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e31 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e31
        | exact resolve b0e31 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e230 : ∀ X0 X1 X3 : G, (M.op X3 (σ y)) = (M.op (M.op (M.op X0 X1) (σ y)) X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e31 X3 (M.op X0 x)
           have i₂ := b0e11 (σ y) X0 x X1
           grind)
        | exact superpose b0e11 b0e31
        | exact resolve b0e31 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e241 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ y) X1 x
           have i₂ := b0e31 X0 x
           grind)
        | exact superpose b0e31 b0e11
        | exact resolve b0e11 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e260 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e241 X0 x
           have i₂ := b0e81 (σ y) X0 x
           grind)
        | exact superpose b0e81 b0e241
        | exact resolve b0e241 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81 b0e241
      have b0e270 : ∀ X3 : G, (M.op y X3) = (M.op X3 (σ y)) := by
        intro X3
        first
        | (have i₁ := b0e230 x x X3
           have i₂ := b0e80 (M.op x x) X3 (σ y)
           grind)
        | exact superpose b0e80 b0e230
        | exact resolve b0e230 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230
      have b0e305 : (σ y) = (M.op (σ y) y) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e260 (σ y)
           grind)
        | exact superpose b0e260 b0e20
        | exact resolve b0e20 b0e260
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e306 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e260 (σ x)
           grind)
        | exact superpose b0e260 b0e18
        | exact resolve b0e18 b0e260
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e311 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e306
           have i₂ := b0e43 (σ x)
           grind)
        | exact superpose b0e43 b0e306
        | exact resolve b0e306 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e306
      have b0e312 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e305
           have i₂ := b0e229 y
           grind)
        | exact superpose b0e229 b0e305
        | exact resolve b0e305 b0e229
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e229 b0e305
      have b0e322 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e311
           have i₂ := b0e43 x
           grind)
        | exact superpose b0e43 b0e311
        | exact resolve b0e311 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e311
      have b0e323 : (σ y) = (M.op y y) := by
        first
        | (have i₁ := b0e312
           have i₂ := b0e260 y
           grind)
        | exact superpose b0e260 b0e312
        | exact resolve b0e312 b0e260
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e260 b0e312
      have b0e333 : y = (σ y) := by
        first
        | (have i₁ := b0e323
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e323
        | exact resolve b0e323 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e323
      have b0e542 : y = (τ y) := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e333
           grind)
        | exact superpose b0e333 b0e12
        | exact resolve b0e12 b0e333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4381 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e97 (σ X1) X2 (σ X0)
           grind)
        | exact superpose b0e97 b0e17
        | (have j1 := b0e97 (σ X1) X2 (σ X0)
           grind)
        | exact resolve b0e17 b0e97
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97
      have b0e7172 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e221 y X0
           have i₂ := b0e333
           grind)
        | exact superpose b0e333 b0e221
        | exact resolve b0e221 b0e333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e7318 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X1) (σ X0)
           have i₂ := b0e88 X1 X0
           grind)
        | exact superpose b0e88 b0e15
        | (have j0 := b0e15 (σ X1) (σ X0)
           have j1 := b0e88 X1 X0
           grind)
        | (have r₁ := b0e15 (σ X1) (σ X1)
           have r₂ := b0e88 X0 X1
           grind)
        | (have r₁ := b0e15 (σ X0) (σ X1)
           have r₂ := b0e88 X0 X1
           grind)
        | exact resolve b0e15 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e7336 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (M.op (M.op (σ X0) X2) (σ X0)) ∨ (σ X0) = (k X3 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e41 (σ X1) X1 (σ X0) X3
           have i₂ := b0e88 X0 X1
           grind)
        | exact superpose b0e88 b0e41
        | (have j1 := b0e88 X1 X0
           grind)
        | exact resolve b0e41 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e7348 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e88 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e7349 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e7348 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7348
      have b0e7351 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e7318 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7318
      have b0e7352 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e7351 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7351
      have b0e7360 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (M.op (M.op (σ X0) X2) (σ X0)) ∨ (σ X0) = (k X3 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b0e7336 X0 X1 X2 X3
           have j1 := b0e14 X3 (σ X0)
           grind)
        | (have r₁ := b0e7336 X0 X1 X2 X3
           have r₂ := b0e14 X0 (σ X0)
           grind)
        | exact resolve b0e7336 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7336
      have b0e7378 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e7352 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e7352
        | (have j0 := b0e7352 X0 X1
           grind)
        | exact resolve b0e7352 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7352
      have b0e7451 : ∀ X0 X1 X3 : G, (σ X0) ≠ (M.op y (σ X0)) ∨ (σ X0) = (k X3 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e7360 X0 X1 x X3
           have i₂ := b0e80 (σ X0) (σ X0) x
           grind)
        | exact superpose b0e80 b0e7360
        | (have j0 := b0e7360 X0 X1 x X3
           grind)
        | exact resolve b0e7360 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80 b0e7360
      have b0e7517 : ∀ X0 X1 : G, (k y (τ (M.op X0 X1))) = (τ (M.op y y)) ∨ (M.op X0 X1) = (M.op y y) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e7172 (M.op X0 X1)
           have i₂ := b0e130 X0 X1 y
           grind)
        | exact superpose b0e130 b0e7172
        | (have j1 := b0e130 X0 X1 y
           grind)
        | exact resolve b0e7172 b0e130
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130 b0e7172
      have b0e7532 : ∀ X0 X1 : G, (τ y) = (k y (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op y y) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e7517 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e7517
        | (have j0 := b0e7517 X0 X1
           grind)
        | exact resolve b0e7517 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7517
      have b0e7534 : ∀ X0 X1 : G, y = (k y (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op y y) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e7532 X0 X1
           have i₂ := b0e542
           grind)
        | exact superpose b0e542 b0e7532
        | (have j0 := b0e7532 X0 X1
           grind)
        | exact resolve b0e7532 b0e542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e542 b0e7532
      have b0e7535 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ y = (k y (τ (M.op X0 X1))) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e7534 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e7534
        | (have j0 := b0e7534 X0 X1
           grind)
        | exact resolve b0e7534 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7534
      have b0e7536 : ∀ X0 X1 : G, y = (k y (τ (M.op X0 X1))) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have j0 := b0e7535 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7535
      have b0e10015 : ∀ X0 X1 : G, (σ y) = (k (σ y) (M.op X0 X1)) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e26 (M.op X0 X1) y
           have i₂ := b0e7536 X0 X1
           grind)
        | exact superpose b0e7536 b0e26
        | (have j1 := b0e7536 X0 X1
           grind)
        | exact resolve b0e26 b0e7536
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7536
      have b0e10023 : ∀ X0 X1 : G, y = (k y (M.op X0 X1)) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b0e10015 X0 X1
           have i₂ := b0e333
           grind)
        | exact superpose b0e333 b0e10015
        | (have j0 := b0e10015 X0 X1
           grind)
        | exact resolve b0e10015 b0e333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10015
      have b0e10904 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e7349 (τ X0)
           have i₂ := b0e25 X0 (τ X0)
           grind)
        | exact superpose b0e25 b0e7349
        | (have j0 := b0e7349 (τ X0)
           grind)
        | exact resolve b0e7349 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e7349
      have b0e10913 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e10904 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e10904
        | (have j0 := b0e10904 X0
           grind)
        | exact resolve b0e10904 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10904
      have b0e10922 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e10913 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e10913
        | (have j0 := b0e10913 X0
           grind)
        | exact resolve b0e10913 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10913
      have b0e19925 : ∀ X0 X1 : G, (σ X0) = (M.op y (σ X0)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e270 (σ X0)
           have i₂ := b0e4381 y X0 X1
           grind)
        | exact superpose b0e4381 b0e270
        | (have j1 := b0e4381 y X0 X1
           grind)
        | exact resolve b0e270 b0e4381
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270 b0e4381
      have b0e20020 : ∀ X0 X1 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e19925 X0 X1
           have j1 := b0e7451 X0 y X1
           grind)
        | (have r₁ := b0e19925 X0 X1
           have r₂ := b0e7451 X0 X1 x
           grind)
        | exact resolve b0e19925 b0e7451
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7451 b0e19925
      have b0e20114 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e20020 X0 X1
           have i₂ := b0e333
           grind)
        | exact superpose b0e333 b0e20020
        | (have j0 := b0e20020 X0 X1
           grind)
        | exact resolve b0e20020 b0e333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20020
      have b0e26389 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e7378 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7378
      have b0e26391 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e26389 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26389
      have b0e39911 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op y X0) = (σ (k y (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e20114 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e20114
        | exact resolve b0e20114 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40014 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e221 X1 (σ X0)
           have i₂ := b0e20114 X0 (σ X1)
           grind)
        | exact superpose b0e20114 b0e221
        | (have j1 := b0e20114 X0 X1
           grind)
        | exact resolve b0e221 b0e20114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e221 b0e20114
      have b0e40047 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40014 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e40014
        | (have j0 := b0e40014 X0 X1
           grind)
        | exact resolve b0e40014 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40014
      have b0e40074 : ∀ X0 X1 : G, (M.op y X0) = (k (σ y) X0) ∨ (k X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e39911 X0 X1
           have i₂ := b0e26 X0 y
           grind)
        | exact superpose b0e26 b0e39911
        | (have j0 := b0e39911 X0 X1
           grind)
        | exact resolve b0e39911 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39911
      have b0e40082 : ∀ X0 X1 : G, (M.op y X0) = (k y X0) ∨ (k X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e40074 X0 X1
           have i₂ := b0e333
           grind)
        | exact superpose b0e333 b0e40074
        | (have j0 := b0e40074 X0 X1
           grind)
        | exact resolve b0e40074 b0e333
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e333 b0e40074
      have b0e40677 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e10922 X0
           have i₂ := b0e40082 X0 X0
           grind)
        | exact superpose b0e40082 b0e10922
        | (have j0 := b0e10922 X0
           have j1 := b0e40082 X0 x
           grind)
        | (have r₁ := b0e10922 X0
           have r₂ := b0e40082 X0 X0
           grind)
        | exact resolve b0e10922 b0e40082
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10922 b0e40082
      have b0e40804 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e40677 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40677
      have b0e46717 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e40047 X0 X1
           have i₂ := b0e40804 X0
           grind)
        | exact superpose b0e40804 b0e40047
        | (have j0 := b0e40047 X0 X1
           have j1 := b0e40804 X0
           grind)
        | exact resolve b0e40047 b0e40804
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40047 b0e40804
      have b0e47132 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (k X1 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e46717 X0 X1
           have j1 := b0e14 X1 X0
           grind)
        | (have r₁ := b0e46717 X1 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e46717 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46717
      have b0e57699 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e26391 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e26391
        | exact resolve b0e26391 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26391
      have b0e57918 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e57699 X0
           have i₂ := b0e26 X0 (τ X0)
           grind)
        | exact superpose b0e26 b0e57699
        | (have j0 := b0e57699 X0
           grind)
        | exact resolve b0e57699 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e57699
      have b0e57939 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e57918 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e57918
        | (have j0 := b0e57918 X0
           grind)
        | exact resolve b0e57918 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57918
      have b0e59540 : ∀ X0 : G, (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e322
           have i₂ := b0e47132 x X0
           grind)
        | exact superpose b0e47132 b0e322
        | (have j1 := b0e47132 x X0
           grind)
        | (have r₁ := b0e322
           have r₂ := b0e47132 x x
           grind)
        | exact resolve b0e322 b0e47132
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e322 b0e47132
      have b0e59792 : ∀ X0 : G, x = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e59540 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59540
      have b0e60639 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e57939 x
           have i₂ := b0e59792 x
           grind)
        | exact superpose b0e59792 b0e57939
        | (have j0 := b0e57939 x
           grind)
        | exact resolve b0e57939 b0e59792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57939
      have b0e60702 : x = (M.op x x) := by grind
      clear b0e60639
      have b0e61420 : y = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e10023 x x
           have i₂ := b0e60702
           grind)
        | exact superpose b0e60702 b0e10023
        | exact resolve b0e10023 b0e60702
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10023 b0e60702
      have b0e61448 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e61420
           have i₂ := b0e59792 y
           grind)
        | exact superpose b0e59792 b0e61420
        | exact resolve b0e61420 b0e59792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59792 b0e61420
      have b0e61449 : x = y := by grind
      clear b0e61448
      have b0e62413 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e61449
           grind)
        | exact superpose b0e61449 b0e18
        | exact resolve b0e18 b0e61449
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61449
      have b0e62414 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e62413
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e62413
        | exact resolve b0e62413 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62413
      have b0e62417 : False := by grind
      exact b0e62417
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
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
        have b1e24 : ∀ X0 : G, y = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e59 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e60 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e59
        have b1e61 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e60
             have r₂ := b1e21
             grind)
          | exact resolve b1e60 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e63 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e61
          | exact resolve b1e61 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e65 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e24 x
             grind)
          | exact superpose b1e24 b1e63
          | exact resolve b1e63 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e63
        have b1e67 : False := by grind
        exact b1e67
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
          intro X0 X1 X2 X3
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
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
        have b2e24 : ∀ X0 : G, y = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
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
        have b2e27 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y y X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y X1 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X2 X5)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b2e12 (M.op X0 X1) X2 X3 X5
             have i₂ := b2e12 (M.op X2 X5) X0 X1 X4
             grind)
          | (have i₁ := b2e12 X0 X1 X2 X3
             have i₂ := b2e12 X0 X1 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e27 X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e27
          | exact resolve b2e27 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X0 X2 y
             have i₂ := b2e39 X0
             grind)
          | (have i₁ := b2e12 X0 y X2 X0
             have i₂ := b2e39 X0
             grind)
          | exact superpose b2e39 b2e12
          | exact resolve b2e12 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e77 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e66 X0 X1 X2
             have i₂ := b2e27 X1 X0
             grind)
          | exact superpose b2e27 b2e66
          | exact resolve b2e66 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e66
        have b2e86 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X2)) ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X0 X2 X0
             have i₂ := b2e17 X3 X0
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X3 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e98 : ∀ X0 X1 X3 : G, (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X1) = (M.op X1 y) ∨ (M.op X0 X3) = X0 := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e86 X0 X1 x X3
             have i₂ := b2e77 X0 X1 x
             grind)
          | exact superpose b2e77 b2e86
          | (have j0 := b2e86 X0 X1 x X3
             grind)
          | exact resolve b2e86 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e184 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e4285 : ∀ X0 : G, (τ y) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b2e184 X0 y
             have i₂ := b2e24 (σ X0)
             grind)
          | exact superpose b2e24 b2e184
          | exact resolve b2e184 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e184
        have b2e4464 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e98 X0 x y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e4465 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e4464 X0
             have j1 := b2e17 y X0
             grind)
          | (have r₁ := b2e4464 x
             have r₂ := b2e17 X0 x
             grind)
          | (have r₁ := b2e4464 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e4464 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4464
        have b2e8087 : (τ y) = (M.op y (τ y)) ∨ (τ y) = (M.op (τ y) y) := by
          first
          | (have i₁ := b2e4285 y
             have i₂ := b2e4465 (τ y)
             grind)
          | exact superpose b2e4465 b2e4285
          | (have j1 := b2e4465 (τ y)
             grind)
          | exact resolve b2e4285 b2e4465
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4285 b2e4465
        have b2e8094 : (τ y) = (M.op y (τ y)) ∨ (τ y) = (M.op y (τ y)) := by
          first
          | (have i₁ := b2e8087
             have i₂ := b2e39 (τ y)
             grind)
          | exact superpose b2e39 b2e8087
          | exact resolve b2e8087 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8087
        have b2e8095 : (τ y) = (M.op y (τ y)) := by grind
        clear b2e8094
        have b2e8127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op (τ y) (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e36 y X0 X1 X2 (τ y) X3
             have i₂ := b2e8095
             grind)
          | exact superpose b2e8095 b2e36
          | exact resolve b2e36 b2e8095
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e8149 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op (τ y) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e8127 X0 X1 X2 x
             have i₂ := b2e77 X1 (τ y) x
             grind)
          | exact superpose b2e77 b2e8127
          | exact resolve b2e8127 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8127
        have b2e8168 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (M.op y (τ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e8149 X0 X1 X2
             have i₂ := b2e39 (τ y)
             grind)
          | exact superpose b2e39 b2e8149
          | exact resolve b2e8149 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8149
        have b2e8173 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) (M.op X1 X2)) = (τ y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e8168 X0 X1 X2
             have i₂ := b2e8095
             grind)
          | exact superpose b2e8095 b2e8168
          | exact resolve b2e8168 b2e8095
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8095 b2e8168
        have b2e8176 : ∀ X0 : G, (M.op (M.op y X0) y) = (τ y) := by
          intro X0
          first
          | (have i₁ := b2e8173 X0 x x
             have i₂ := b2e77 x (M.op y X0) x
             grind)
          | exact superpose b2e77 b2e8173
          | exact resolve b2e8173 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77 b2e8173
        have b2e8179 : ∀ X0 : G, (M.op y (M.op y X0)) = (τ y) := by
          intro X0
          first
          | (have i₁ := b2e8176 X0
             have i₂ := b2e39 (M.op y X0)
             grind)
          | exact superpose b2e39 b2e8176
          | exact resolve b2e8176 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e8176
        have b2e8182 : (M.op y y) = (τ y) := by
          first
          | (have i₁ := b2e8179 x
             have i₂ := b2e32 y x
             grind)
          | exact superpose b2e32 b2e8179
          | exact resolve b2e8179 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e8179
        have b2e8185 : y = (τ y) := by
          first
          | (have i₁ := b2e8182
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e8182
          | exact resolve b2e8182 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8182
        have b2e8259 : y = (σ y) := by
          first
          | (have i₁ := b2e14 y
             have i₂ := b2e8185
             grind)
          | exact superpose b2e8185 b2e14
          | exact resolve b2e14 b2e8185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8185
        have b2e8284 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e8259
             grind)
          | exact superpose b2e8259 b2e21
          | exact resolve b2e21 b2e8259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8259
        have b2e8305 : False := by grind
        exact b2e8305
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) := by
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
        have b3e24 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e28 : ∀ X0 : G, (σ y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e24 (σ X0)
             have i₂ := b3e18 X0 y
             grind)
          | exact superpose b3e18 b3e24
          | exact resolve b3e24 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e31 : ∀ X0 : G, (k X0 y) = (τ (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e28 X0
             grind)
          | exact superpose b3e28 b3e13
          | exact resolve b3e13 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e32 : ∀ X0 : G, y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e66 : y ≠ y ∨ y = (M.op y y) ∨ (M.op y y) = (k x y) := by
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
        have b3e67 : y = (M.op y y) ∨ (M.op y y) = (k x y) := by grind
        clear b3e66
        have b3e68 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e67
             have r₂ := b3e20
             grind)
          | exact resolve b3e67 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e70 : y = (M.op y y) := by
          first
          | (have i₁ := b3e68
             have i₂ := b3e32 x
             grind)
          | exact superpose b3e32 b3e68
          | exact resolve b3e68 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e68
        have b3e72 : False := by grind
        exact b3e72
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
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
          have b4e30 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e30 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e30
            | exact resolve b4e30 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e98 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X0 y X2
               have i₂ := b4e41 X0
               grind)
            | (have i₁ := b4e13 X0 y X0 x
               have i₂ := b4e41 X0
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X1 X0
               have i₂ := b4e41 X0
               grind)
            | (have i₁ := b4e30 X0 y
               have i₂ := b4e41 y
               grind)
            | exact superpose b4e41 b4e30
            | exact resolve b4e30 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e108 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e98 X0 X1 X2
               have i₂ := b4e36 X1 X0
               grind)
            | exact superpose b4e36 b4e98
            | exact resolve b4e98 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e98
          have b4e293 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e29 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e29
            | exact resolve b4e29 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e295 : ∀ X0 X1 X3 : G, (M.op X3 (σ y)) = (M.op (M.op (M.op X0 X1) (σ y)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e29 X3 (M.op X0 x)
               have i₂ := b4e13 (σ y) X0 x X1
               grind)
            | exact superpose b4e13 b4e29
            | exact resolve b4e29 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e310 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e101 (σ y) X0
               have i₂ := b4e29 X0 y
               grind)
            | exact superpose b4e29 b4e101
            | exact resolve b4e101 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e101
          have b4e343 : ∀ X3 : G, (M.op y X3) = (M.op X3 (σ y)) := by
            intro X3
            first
            | (have i₁ := b4e295 x x X3
               have i₂ := b4e108 (M.op x x) X3 (σ y)
               grind)
            | exact superpose b4e108 b4e295
            | exact resolve b4e295 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108 b4e295
          have b4e345 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e293 X0
               have i₂ := b4e310 X0
               grind)
            | exact superpose b4e310 b4e293
            | exact resolve b4e293 b4e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293 b4e310
          have b4e404 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e343 (σ x)
               grind)
            | exact superpose b4e343 b4e20
            | exact resolve b4e20 b4e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343
          have b4e410 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e404
               have i₂ := b4e41 x
               grind)
            | exact superpose b4e41 b4e404
            | exact resolve b4e404 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e404
          have b4e425 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e410
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e410
            | exact resolve b4e410 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e410
          have b4e947 : (σ y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e345 (σ x)
               grind)
            | exact superpose b4e345 b4e24
            | exact resolve b4e24 b4e345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e345
          have b4e987 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e947
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e947
            | exact resolve b4e947 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e947
          have b4e1007 : False := by grind
          exact b4e1007
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e27 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y x X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op X0 X2) = (k X3 (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e16 X3 (M.op X0 X2)
               have i₂ := b5e13 (M.op X0 X2) X0 X2 X1
               grind)
            | (have i₁ := b5e16 X0 (M.op X1 X3)
               have i₂ := b5e13 (M.op X1 X3) X1 X2 X3
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 X3 (M.op X0 X2)
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e27
            | exact resolve b5e27 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op (M.op y X0) y) ∨ (M.op y X0) = (k X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 (M.op y X0)
               have i₂ := b5e27 (M.op y X0) X0
               grind)
            | exact superpose b5e27 b5e16
            | (have j0 := b5e16 X1 (M.op y X0)
               grind)
            | exact resolve b5e16 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : ∀ X0 X1 : G, (M.op y y) ≠ (M.op y X0) ∨ (M.op y X0) = (k X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e44 X0 X1
               have i₂ := b5e27 y X0
               grind)
            | exact superpose b5e27 b5e44
            | (have j0 := b5e44 X0 X1
               grind)
            | (have r₁ := b5e44 y X1
               have r₂ := b5e27 y y
               grind)
            | exact resolve b5e44 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e70 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X2 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X2 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b5e76 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e78 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e70 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e90 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 X2 y
               have i₂ := b5e39 X0
               grind)
            | (have i₁ := b5e13 X0 y X2 X0
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e91 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 y X2
               have i₂ := b5e39 X0
               grind)
            | (have i₁ := b5e13 X0 y X0 x
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e96 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) X1) = (M.op X1 (M.op y X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 y X2 X0
               have i₂ := b5e39 X0
               grind)
            | (have i₁ := b5e13 X0 X0 X2 y
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e97 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op y X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 y X0 X2
               have i₂ := b5e39 X0
               grind)
            | (have i₁ := b5e13 X0 X0 y x
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e98 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e97 X0 X1 x
               have i₂ := b5e27 X1 x
               grind)
            | exact superpose b5e27 b5e97
            | exact resolve b5e97 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e99 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e96 X0 X1 x
               have i₂ := b5e32 X1 x
               grind)
            | exact superpose b5e32 b5e96
            | exact resolve b5e96 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e101 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e91 X0 X1 X2
               have i₂ := b5e32 X1 X0
               grind)
            | exact superpose b5e32 b5e91
            | exact resolve b5e91 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e102 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e90 X0 X1 X2
               have i₂ := b5e27 X1 X0
               grind)
            | exact superpose b5e27 b5e90
            | exact resolve b5e90 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e229 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e26 X1 X0
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e242 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 y X2
               have i₂ := b5e98 X1 X0
               grind)
            | exact superpose b5e98 b5e13
            | exact resolve b5e13 b5e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e450 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2 y
               have i₂ := b5e99 X1 X0
               grind)
            | exact superpose b5e99 b5e13
            | exact resolve b5e13 b5e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e3841 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 y
               have i₂ := b5e77 (σ X0)
               grind)
            | exact superpose b5e77 b5e19
            | (have j1 := b5e77 (σ X0)
               grind)
            | exact resolve b5e19 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e3869 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e78 (σ X1) X2 (σ X0)
               grind)
            | exact superpose b5e78 b5e19
            | (have j1 := b5e78 (σ X1) X2 (σ X0)
               grind)
            | exact resolve b5e19 b5e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e4117 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e37 X0 X0 X1 X2
               have i₂ := b5e18 X3 X0
               grind)
            | exact superpose b5e18 b5e37
            | (have j0 := b5e37 X0 X1 X1 X2
               have j1 := b5e18 X3 X0
               grind)
            | (have r₁ := b5e37 X0 X2 X2 X3
               have r₂ := b5e18 X0 (M.op X0 X2)
               grind)
            | (have r₁ := b5e37 X0 X2 X2 X3
               have r₂ := b5e18 (M.op X0 X2) (M.op X0 X2)
               grind)
            | exact resolve b5e37 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4259 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 y) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e4117 X0 X1 X2 X3
               have i₂ := b5e102 X0 X0 X1
               grind)
            | exact superpose b5e102 b5e4117
            | (have j0 := b5e4117 X0 X1 X2 X3
               grind)
            | (have r₁ := b5e4117 X0 y X2 X3
               have r₂ := b5e102 X0 X0 y
               grind)
            | exact resolve b5e4117 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102 b5e4117
          have b5e6404 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (M.op (M.op (σ X0) X2) (σ X0)) ∨ (σ X0) = (k X3 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e37 (σ X1) X1 (σ X0) X3
               have i₂ := b5e68 X0 X1
               grind)
            | exact superpose b5e68 b5e37
            | (have j1 := b5e68 X1 X0
               grind)
            | exact resolve b5e37 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e6416 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e68 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68
          have b5e6417 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e6416 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6416
          have b5e6429 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (M.op (M.op (σ X0) X2) (σ X0)) ∨ (σ X0) = (k X3 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b5e6404 X0 X1 X2 X3
               have j1 := b5e16 X3 (σ X0)
               grind)
            | (have r₁ := b5e6404 X0 X1 X2 X3
               have r₂ := b5e16 X0 (σ X0)
               grind)
            | exact resolve b5e6404 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6404
          have b5e6501 : ∀ X0 X1 X3 : G, (σ X0) ≠ (M.op y (σ X0)) ∨ (σ X0) = (k X3 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e6429 X0 X1 x X3
               have i₂ := b5e101 (σ X0) (σ X0) x
               grind)
            | exact superpose b5e101 b5e6429
            | (have j0 := b5e6429 X0 X1 x X3
               grind)
            | exact resolve b5e6429 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6429
          have b5e10128 : ∀ X0 : G, (M.op y y) = (k X0 (M.op y y)) := by
            intro X0
            first
            | (have j0 := b5e51 y X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e10143 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e6417 (M.op y y)
               have i₂ := b5e10128 (M.op y y)
               grind)
            | exact superpose b5e10128 b5e6417
            | (have j0 := b5e6417 (M.op y y)
               grind)
            | exact resolve b5e6417 b5e10128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6417 b5e10128
          have b5e10158 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
          clear b5e10143
          have b5e10313 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e17 (σ X0) (σ y)
               have i₂ := b5e3841 X0
               grind)
            | exact superpose b5e3841 b5e17
            | (have j0 := b5e17 (σ X0) (σ y)
               have j1 := b5e3841 X0
               grind)
            | (have r₁ := b5e17 (σ X0) (σ y)
               have r₂ := b5e3841 X0
               grind)
            | exact resolve b5e17 b5e3841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3841
          have b5e10352 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e10313 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10313
          have b5e10379 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e10352 X0
               grind)
            | (have r₁ := b5e10352 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e10352 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10352
          have b5e10427 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k X0 y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e10379 X0
               have i₂ := b5e19 X0 y
               grind)
            | exact superpose b5e19 b5e10379
            | (have j0 := b5e10379 X0
               grind)
            | exact resolve b5e10379 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10379
          have b5e11340 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e101 (σ (M.op y y)) X0 (σ (M.op y y))
               have i₂ := b5e10158
               grind)
            | exact superpose b5e10158 b5e101
            | exact resolve b5e101 b5e10158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e11342 : ∀ X0 : G, (M.op X0 y) = (M.op (σ (M.op y y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e242 X0 (σ (M.op y y)) (σ (M.op y y))
               have i₂ := b5e10158
               grind)
            | exact superpose b5e10158 b5e242
            | exact resolve b5e242 b5e10158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242
          have b5e11344 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e450 X0 (σ (M.op y y)) (σ (M.op y y))
               have i₂ := b5e10158
               grind)
            | exact superpose b5e10158 b5e450
            | exact resolve b5e450 b5e10158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e450
          have b5e11908 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
            first
            | (have i₁ := b5e10158
               have i₂ := b5e11340 (σ (M.op y y))
               grind)
            | exact superpose b5e11340 b5e10158
            | exact resolve b5e10158 b5e11340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10158 b5e11340
          have b5e12035 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e11908
               have i₂ := b5e11344 y
               grind)
            | exact superpose b5e11344 b5e11908
            | exact resolve b5e11908 b5e11344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11908
          have b5e12772 : ∀ X0 : G, (σ (k (M.op y y) X0)) = (k (M.op y y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 (M.op y y) X0
               have i₂ := b5e12035
               grind)
            | exact superpose b5e12035 b5e19
            | exact resolve b5e19 b5e12035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e12788 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (M.op y y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e229 (M.op y y) X0
               have i₂ := b5e12035
               grind)
            | exact superpose b5e12035 b5e229
            | exact resolve b5e229 b5e12035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e18980 : ∀ X0 X1 : G, (σ X0) = (M.op y (σ X0)) ∨ (M.op (σ (M.op y y)) (σ X0)) = (σ (k (M.op y y) X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e11344 (σ X0)
               have i₂ := b5e3869 (M.op y y) X0 X1
               grind)
            | exact superpose b5e3869 b5e11344
            | (have j1 := b5e3869 (M.op y y) X0 X1
               grind)
            | exact resolve b5e11344 b5e3869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3869 b5e11344
          have b5e19070 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) (σ X0)) = (σ (k (M.op y y) X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e18980 X0 X1
               have j1 := b5e6501 X0 (M.op y y) X1
               grind)
            | (have r₁ := b5e18980 X0 X1
               have r₂ := b5e6501 X0 X1 x
               grind)
            | exact resolve b5e18980 b5e6501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6501 b5e18980
          have b5e19151 : ∀ X0 X1 : G, (M.op (σ X0) y) = (σ (k (M.op y y) X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19070 X0 X1
               have i₂ := b5e11342 (σ X0)
               grind)
            | exact superpose b5e11342 b5e19070
            | (have j0 := b5e19070 X0 X1
               grind)
            | exact resolve b5e19070 b5e11342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11342 b5e19070
          have b5e19183 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19151 X0 X1
               have i₂ := b5e39 (σ X0)
               grind)
            | exact superpose b5e39 b5e19151
            | (have j0 := b5e19151 X0 X1
               grind)
            | exact resolve b5e19151 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19151
          have b5e22562 : ∀ X0 X1 X2 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k X1 (M.op y X0)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4259 X0 y X2 x
               have i₂ := b5e39 X0
               grind)
            | (have i₁ := b5e4259 y X0 X2 x
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e4259
            | (have j0 := b5e4259 X0 X1 X2 X2
               grind)
            | (have r₁ := b5e4259 y y X2 x
               have r₂ := b5e39 y
               grind)
            | exact resolve b5e4259 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4259
          have b5e22629 : ∀ X0 X1 X2 : G, (M.op y X0) = (k X1 (M.op y X0)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e22562 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22562
          have b5e67494 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have j0 := b5e10427 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10427
          have b5e67495 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
          clear b5e67494
          have b5e68156 : (σ y) ≠ (σ (k y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e67495
               grind)
            | exact superpose b5e67495 b5e23
            | exact resolve b5e23 b5e67495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67495
          have b5e78512 : ∀ X0 X1 : G, (k X1 x) = (M.op X1 x) ∨ y = (k X0 y) ∨ x = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e22629 x X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e22629
            | (have j0 := b5e22629 x X1 X1
               grind)
            | exact resolve b5e22629 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22629
          have b5e79392 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 x) = (k X0 x) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e68156
               have i₂ := b5e78512 y X0
               grind)
            | exact superpose b5e78512 b5e68156
            | (have j1 := b5e78512 X0 X0
               grind)
            | exact resolve b5e68156 b5e78512
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68156 b5e78512
          have b5e79406 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b5e79392 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79392
          have b5e79665 : (k (M.op y y) (τ x)) = (τ (M.op (M.op y y) x)) ∨ x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e12788 x
               have i₂ := b5e79406 (M.op y y)
               grind)
            | exact superpose b5e79406 b5e12788
            | (have j1 := b5e79406 (M.op y y)
               grind)
            | exact resolve b5e12788 b5e79406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12788 b5e79406
          have b5e79691 : (τ (M.op x y)) = (k (M.op y y) (τ x)) ∨ x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e79665
               have i₂ := b5e27 x y
               grind)
            | exact superpose b5e27 b5e79665
            | exact resolve b5e79665 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e79665
          have b5e79693 : (τ (M.op y x)) = (k (M.op y y) (τ x)) ∨ x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e79691
               have i₂ := b5e39 x
               grind)
            | exact superpose b5e39 b5e79691
            | exact resolve b5e79691 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e79691
          have b5e79695 : (τ y) = (k (M.op y y) (τ x)) ∨ x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e79693
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e79693
            | exact resolve b5e79693 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79693
          have b5e79697 : x = (M.op y x) ∨ (τ y) = (k (M.op y y) (τ x)) := by
            first
            | (have i₁ := b5e79695
               have i₂ := b5e32 x y
               grind)
            | exact superpose b5e32 b5e79695
            | exact resolve b5e79695 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e79695
          have b5e79699 : (τ y) = (k (M.op y y) (τ x)) ∨ x = y := by
            first
            | (have i₁ := b5e79697
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e79697
            | exact resolve b5e79697 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79697
          have b5e80366 : (σ (τ y)) = (k (σ (M.op y y)) x) ∨ x = y := by
            first
            | (have i₁ := b5e26 x (M.op y y)
               have i₂ := b5e79699
               grind)
            | exact superpose b5e79699 b5e26
            | exact resolve b5e26 b5e79699
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79699
          have b5e80479 : (σ (τ y)) = (k (M.op y y) x) ∨ x = y := by
            first
            | (have i₁ := b5e80366
               have i₂ := b5e12035
               grind)
            | exact superpose b5e12035 b5e80366
            | exact resolve b5e80366 b5e12035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80366
          have b5e80553 : y = (k (M.op y y) x) ∨ x = y := by
            first
            | (have i₁ := b5e80479
               have i₂ := b5e15 y
               grind)
            | exact superpose b5e15 b5e80479
            | exact resolve b5e80479 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80479
          have b5e954089 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op y X0) = (σ (k (M.op y y) (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e19183 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19183
            | exact resolve b5e19183 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19183
          have b5e954098 : ∀ X0 X1 : G, (M.op y X0) = (k (σ (M.op y y)) X0) ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e954089 X0 X1
               have i₂ := b5e26 X0 (M.op y y)
               grind)
            | exact superpose b5e26 b5e954089
            | (have j0 := b5e954089 X0 X1
               grind)
            | exact resolve b5e954089 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e954089
          have b5e954102 : ∀ X0 X1 : G, (M.op y X0) = (k (M.op y y) X0) ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e954098 X0 X1
               have i₂ := b5e12035
               grind)
            | exact superpose b5e12035 b5e954098
            | (have j0 := b5e954098 X0 X1
               grind)
            | exact resolve b5e954098 b5e12035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12035 b5e954098
          have b5e954341 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op y X0) = (k (M.op y y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e229 X1 X0
               have i₂ := b5e954102 X0 (σ X1)
               grind)
            | exact superpose b5e954102 b5e229
            | (have j1 := b5e954102 X0 X1
               grind)
            | exact resolve b5e229 b5e954102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e229 b5e954102
          have b5e960625 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op y (σ X0)) = (k (M.op y y) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e954341 (σ X0) X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e954341
            | (have j0 := b5e954341 (σ X0) X1
               grind)
            | exact resolve b5e954341 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e954341
          have b5e960847 : ∀ X0 X1 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e960625 X0 X1
               have i₂ := b5e12772 X0
               grind)
            | exact superpose b5e12772 b5e960625
            | (have j0 := b5e960625 X0 X1
               grind)
            | exact resolve b5e960625 b5e12772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12772 b5e960625
          have b5e961697 : x = y ∨ (σ y) = (M.op y (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e960847 x (M.op y y)
               have i₂ := b5e80553
               grind)
            | exact superpose b5e80553 b5e960847
            | exact resolve b5e960847 b5e80553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80553 b5e960847
          have b5e962176 : (σ y) = (M.op y (σ x)) ∨ x = y := by grind
          clear b5e961697
          have b5e962231 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e101 y X0 (σ x)
               have i₂ := b5e962176
               grind)
            | exact superpose b5e962176 b5e101
            | exact resolve b5e101 b5e962176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101
          have b5e962326 : (σ y) ≠ (M.op y (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e962231 (σ x)
               grind)
            | exact superpose b5e962231 b5e24
            | exact resolve b5e24 b5e962231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e962231
          have b5e962514 : x = y := by
            first
            | (have r₁ := b5e962326
               have r₂ := b5e962176
               grind)
            | exact resolve b5e962326 b5e962176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e962176 b5e962326
          have b5e962589 : y = (M.op y y) := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e962514
               grind)
            | exact superpose b5e962514 b5e22
            | exact resolve b5e22 b5e962514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e962514
          have b5e962681 : False := by grind
          exact b5e962681
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) := by
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
        have b6e24 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e28 : ∀ X0 : G, (σ y) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e24 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e31 : ∀ X0 : G, (k X0 y) = (τ (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e28 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e32 : ∀ X0 : G, y = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e31 X0
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e69 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y y) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 y y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e79 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b6e69 X0
             grind)
          | (have r₁ := b6e69 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e69 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e69 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e4170 : y ≠ y ∨ y = (M.op y y) := by
          first
          | (have j0 := b6e79 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e4171 : y = (M.op y y) := by grind
        clear b6e4170
        have b6e4176 : False := by grind
        exact b6e4176
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b7e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
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
          have b7e32 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) X1 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2 x
               have i₂ := b7e13 X0 X1 X3 x
               grind)
            | (have i₁ := b7e13 (M.op X1 X2) X1 X2 X3
               have i₂ := b7e13 (M.op X1 X3) X1 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e47 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e47
            | exact resolve b7e47 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e54 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e26 X1 X0
               grind)
            | exact superpose b7e26 b7e14
            | exact resolve b7e14 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X1) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X2 X0
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X0
               have j1 := b7e18 X2 X0
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e70 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e63 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e76 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ (k x y)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) X1 (σ y)
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e13
            | exact resolve b7e13 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e77 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ (k x y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) (σ y) X1
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e13
            | exact resolve b7e13 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e77 X0 x
               have i₂ := b7e27 X0 x
               grind)
            | exact superpose b7e27 b7e77
            | exact resolve b7e77 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e79 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e76 X0 x
               have i₂ := b7e32 X0 x
               grind)
            | exact superpose b7e32 b7e76
            | exact resolve b7e76 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e80 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e27 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e27
            | exact resolve b7e27 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e182 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 X2 (M.op (σ y) x)
               have i₂ := b7e32 X0 x
               grind)
            | exact superpose b7e32 b7e13
            | exact resolve b7e13 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e183 : ∀ X0 X1 X3 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (M.op X0 X3) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e13 X1 X0 (M.op (σ y) x) X3
               have i₂ := b7e32 X0 x
               grind)
            | exact superpose b7e32 b7e13
            | exact resolve b7e13 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e192 : ∀ X0 X1 X3 : G, (M.op (σ y) X1) = (M.op (M.op X0 X3) X1) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e183 X0 X1 X3
               have i₂ := b7e32 X1 X0
               grind)
            | exact superpose b7e32 b7e183
            | exact resolve b7e183 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e183
          have b7e193 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e182 X0 X1 X2
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e182
            | exact resolve b7e182 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27 b7e182
          have b7e272 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X2)) ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e35 X1 X0 X2 X0
               have i₂ := b7e18 X3 X0
               grind)
            | exact superpose b7e18 b7e35
            | (have j1 := b7e18 X3 X0
               grind)
            | exact resolve b7e35 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e327 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op X1 (σ y)) ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = X0 := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e272 X0 X1 x X3
               have i₂ := b7e193 X0 X1 x
               grind)
            | exact superpose b7e193 b7e272
            | (have j0 := b7e272 X0 X1 x X3
               grind)
            | exact resolve b7e272 b7e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e272
          have b7e3206 : ∀ X0 : G, (σ (k x y)) ≠ (M.op (σ (k x y)) (σ y)) ∨ (σ (k x y)) = (k X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e16 X0 (σ (k x y))
               have i₂ := b7e78 (σ (k x y))
               grind)
            | exact superpose b7e78 b7e16
            | (have j0 := b7e16 X0 (σ (k x y))
               grind)
            | exact resolve b7e16 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e3258 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e3206 X0
               have i₂ := b7e79 (σ y)
               grind)
            | exact superpose b7e79 b7e3206
            | (have j0 := b7e3206 X0
               grind)
            | exact resolve b7e3206 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e3206
          have b7e3271 : ∀ X0 : G, (σ (k x y)) = (k X0 (σ (k x y))) := by
            intro X0
            first
            | (have j0 := b7e3258 X0
               grind)
            | (have r₁ := b7e3258 X0
               have r₂ := b7e48
               grind)
            | exact resolve b7e3258 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3258
          have b7e5745 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e60 y y
               grind)
            | exact superpose b7e60 b7e48
            | (have j1 := b7e60 y y
               grind)
            | exact resolve b7e48 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e5867 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e60 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e5868 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e5867 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5867
          have b7e5877 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b7e5745
          have b7e5962 : (σ (k x y)) = (σ (k y y)) := by
            first
            | (have r₁ := b7e5877
               have r₂ := b7e23
               grind)
            | exact resolve b7e5877 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5877
          have b7e6042 : (σ (M.op x y)) = (σ (k y y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e5962
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e5962
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e5962 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6048 : (k x y) = (τ (σ (k y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e5962
               grind)
            | exact superpose b7e5962 b7e14
            | exact resolve b7e14 b7e5962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5962
          have b7e6062 : (k x y) = (k y y) := by
            first
            | (have i₁ := b7e6048
               have i₂ := b7e14 (k y y)
               grind)
            | exact superpose b7e14 b7e6048
            | exact resolve b7e6048 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6048
          have b7e6063 : (σ (M.op x y)) = (σ (k y y)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e6042
               have r₂ := b7e21
               grind)
            | exact resolve b7e6042 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6042
          have b7e6065 : (σ (M.op x y)) = (σ (k y y)) := by
            first
            | (have r₁ := b7e6063
               have r₂ := b7e22
               grind)
            | exact resolve b7e6063 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6063
          have b7e9082 : (M.op x y) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e6062
               grind)
            | exact superpose b7e6062 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e6062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e9083 : (M.op x y) = (k y y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e9082
               have r₂ := b7e21
               grind)
            | exact resolve b7e9082 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9082
          have b7e9087 : (M.op x y) = (k y y) := by
            first
            | (have r₁ := b7e9083
               have r₂ := b7e22
               grind)
            | exact resolve b7e9083 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9083
          have b7e10803 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e9087
               grind)
            | exact superpose b7e9087 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e9087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e10804 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b7e10803
          have b7e10806 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e10804
               have r₂ := b7e21
               grind)
            | exact resolve b7e10804 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10804
          have b7e14386 : ∀ X0 : G, (τ (σ (k x y))) = (k X0 (τ (σ (k x y)))) := by
            intro X0
            first
            | (have i₁ := b7e54 X0 (σ (k x y))
               have i₂ := b7e3271 (σ X0)
               grind)
            | exact superpose b7e3271 b7e54
            | exact resolve b7e54 b7e3271
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3271
          have b7e14389 : ∀ X0 : G, (k x y) = (k X0 (k x y)) := by
            intro X0
            first
            | (have i₁ := b7e14386 X0
               have i₂ := b7e14 (k x y)
               grind)
            | exact superpose b7e14 b7e14386
            | exact resolve b7e14386 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14386
          have b7e14404 : ∀ X0 : G, (k y y) = (k X0 (k y y)) := by
            intro X0
            first
            | (have i₁ := b7e14389 X0
               have i₂ := b7e6062
               grind)
            | exact superpose b7e6062 b7e14389
            | exact resolve b7e14389 b7e6062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6062 b7e14389
          have b7e14419 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b7e14404 X0
               have i₂ := b7e9087
               grind)
            | exact superpose b7e9087 b7e14404
            | exact resolve b7e14404 b7e9087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9087 b7e14404
          have b7e14430 : ∀ X0 : G, (M.op y y) = (k X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e14419 X0
               have i₂ := b7e10806
               grind)
            | exact superpose b7e10806 b7e14419
            | exact resolve b7e14419 b7e10806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14419
          have b7e24777 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e5868 (τ X0)
               have i₂ := b7e25 X0 (τ X0)
               grind)
            | exact superpose b7e25 b7e5868
            | (have j0 := b7e5868 (τ X0)
               grind)
            | exact resolve b7e5868 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e5868
          have b7e24784 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e24777 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e24777
            | (have j0 := b7e24777 X0
               grind)
            | exact resolve b7e24777 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24777
          have b7e24792 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e24784 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e24784
            | (have j0 := b7e24784 X0
               grind)
            | exact resolve b7e24784 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24784
          have b7e24853 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) (M.op y y)) := by
            first
            | (have i₁ := b7e24792 (M.op y y)
               have i₂ := b7e14430 (M.op y y)
               grind)
            | exact superpose b7e14430 b7e24792
            | (have j0 := b7e24792 (M.op y y)
               grind)
            | (have r₁ := b7e24792 (M.op y y)
               have r₂ := b7e14430 (M.op y y)
               grind)
            | exact resolve b7e24792 b7e14430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24792
          have b7e24857 : (M.op y y) = (M.op (M.op y y) (M.op y y)) := by grind
          clear b7e24853
          have b7e24869 : (M.op y y) = (M.op (M.op y y) (σ y)) := by
            first
            | (have i₁ := b7e24857
               have i₂ := b7e193 y (M.op y y) y
               grind)
            | exact superpose b7e193 b7e24857
            | exact resolve b7e24857 b7e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24857
          have b7e24873 : (M.op y y) = (M.op (σ y) (M.op y y)) := by
            first
            | (have i₁ := b7e24869
               have i₂ := b7e80 (M.op y y)
               grind)
            | exact superpose b7e80 b7e24869
            | exact resolve b7e24869 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24869
          have b7e24876 : (M.op y y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e24873
               have i₂ := b7e193 y (σ y) y
               grind)
            | exact superpose b7e193 b7e24873
            | exact resolve b7e24873 b7e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24873
          have b7e24967 : (σ y) ≠ (M.op y y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24876
               grind)
            | exact superpose b7e24876 b7e23
            | exact resolve b7e23 b7e24876
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e24969 : (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e60 y y
               have i₂ := b7e24876
               grind)
            | exact superpose b7e24876 b7e60
            | exact resolve b7e60 b7e24876
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e24876
          have b7e25030 : (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y y) := by grind
          clear b7e24969
          have b7e25071 : (σ (M.op x y)) = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e25030
               have i₂ := b7e6065
               grind)
            | exact superpose b7e6065 b7e25030
            | exact resolve b7e25030 b7e6065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6065 b7e25030
          have b7e25093 : (σ (M.op x y)) = (M.op y y) := by
            first
            | (have r₁ := b7e25071
               have r₂ := b7e24967
               grind)
            | exact resolve b7e25071 b7e24967
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24967 b7e25071
          have b7e25113 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e25093
               have i₂ := b7e10806
               grind)
            | exact superpose b7e10806 b7e25093
            | exact resolve b7e25093 b7e10806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25093
          have b7e25711 : ∀ X0 : G, (σ (k (M.op y y) X0)) = (k (M.op y y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 (M.op y y) X0
               have i₂ := b7e25113
               grind)
            | exact superpose b7e25113 b7e19
            | exact resolve b7e19 b7e25113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26552 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e327 (σ x) (σ y) X0
               grind)
            | exact superpose b7e327 b7e24
            | (have j1 := b7e327 (σ x) x X0
               grind)
            | exact resolve b7e24 b7e327
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26706 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b7e327 X0 x (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e327
          have b7e26708 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b7e26706 X0
               have j1 := b7e18 (σ y) X0
               grind)
            | (have r₁ := b7e26706 x
               have r₂ := b7e18 X0 x
               grind)
            | (have r₁ := b7e26706 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e26706 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26706
          have b7e26758 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b7e26552 X0
               grind)
            | (have r₁ := b7e26552 X0
               have r₂ := b7e23
               grind)
            | exact resolve b7e26552 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26552
          have b7e55531 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e54 y X0
               have i₂ := b7e26708 X0
               grind)
            | exact superpose b7e26708 b7e54
            | (have j1 := b7e26708 X0
               grind)
            | exact resolve b7e54 b7e26708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54 b7e26708
          have b7e76329 : (σ (k (M.op y y) x)) = (M.op (M.op y y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op y y)) := by
            first
            | (have i₁ := b7e25711 x
               have i₂ := b7e26758 (M.op y y)
               grind)
            | exact superpose b7e26758 b7e25711
            | (have j1 := b7e26758 (M.op y y)
               grind)
            | exact resolve b7e25711 b7e26758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25711 b7e26758
          have b7e76361 : (M.op (σ y) (σ x)) = (σ (k (M.op y y) x)) ∨ (σ x) = (M.op (σ x) (M.op y y)) := by
            first
            | (have i₁ := b7e76329
               have i₂ := b7e192 y (σ x) y
               grind)
            | exact superpose b7e192 b7e76329
            | exact resolve b7e76329 b7e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e192 b7e76329
          have b7e76368 : (σ y) = (σ (k (M.op y y) x)) ∨ (σ x) = (M.op (σ x) (M.op y y)) := by
            first
            | (have i₁ := b7e76361
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e76361
            | exact resolve b7e76361 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76361
          have b7e76374 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k (M.op y y) x)) := by
            first
            | (have i₁ := b7e76368
               have i₂ := b7e193 y (σ x) y
               grind)
            | exact superpose b7e193 b7e76368
            | exact resolve b7e76368 b7e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e193 b7e76368
          have b7e76379 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k (M.op y y) x)) := by
            first
            | (have i₁ := b7e76374
               have i₂ := b7e80 (σ x)
               grind)
            | exact superpose b7e80 b7e76374
            | exact resolve b7e76374 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76374
          have b7e76384 : (σ y) = (σ (k (M.op y y) x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e76379
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e76379
            | exact resolve b7e76379 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76379
          have b7e83583 : (τ (σ y)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e55531 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e55531
            | (have j0 := b7e55531 (σ x)
               grind)
            | exact resolve b7e55531 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55531
          have b7e83717 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e83583
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e83583
            | exact resolve b7e83583 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83583
          have b7e83755 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e83717
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e83717
            | exact resolve b7e83717 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83717
          have b7e83791 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e83755
               have i₂ := b7e80 (σ x)
               grind)
            | exact superpose b7e80 b7e83755
            | exact resolve b7e83755 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83755
          have b7e83822 : y = (k y x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e83791
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e83791
            | exact resolve b7e83791 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83791
          have b7e84918 : ∀ X0 : G, y = (M.op y x) ∨ x = (k X0 x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e70 x X0 y
               have i₂ := b7e83822
               grind)
            | exact superpose b7e83822 b7e70
            | (have j0 := b7e70 x X0 y
               grind)
            | exact resolve b7e70 b7e83822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e83822
          have b7e84925 : ∀ X0 : G, x = (k X0 x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b7e84918 X0
               grind)
            | (have r₁ := b7e84918 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e84918 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84918
          have b7e84929 : ∀ X0 : G, x = (k X0 x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e84925 X0
               have i₂ := b7e10806
               grind)
            | exact superpose b7e10806 b7e84925
            | (have j0 := b7e84925 X0
               grind)
            | exact resolve b7e84925 b7e10806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10806 b7e84925
          have b7e86276 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e76384
               have i₂ := b7e84929 (M.op y y)
               grind)
            | exact superpose b7e84929 b7e76384
            | exact resolve b7e76384 b7e84929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84929
          have b7e86297 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e86276
          have b7e86717 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e14430 X0
               have i₂ := b7e86297
               grind)
            | exact superpose b7e86297 b7e14430
            | exact resolve b7e14430 b7e86297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e14430
          have b7e86725 : (σ x) = (σ y) ∨ x = (σ x) := by
            first
            | (have i₁ := b7e25113
               have i₂ := b7e86297
               grind)
            | exact superpose b7e86297 b7e25113
            | exact resolve b7e25113 b7e86297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25113 b7e86297
          have b7e91706 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e86725
               grind)
            | exact superpose b7e86725 b7e24
            | exact resolve b7e24 b7e86725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86725
          have b7e91802 : x = (σ x) := by
            first
            | (have r₁ := b7e91706
               have r₂ := b7e23
               grind)
            | exact resolve b7e91706 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91706
          have b7e92197 : (σ y) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e91802
               grind)
            | exact superpose b7e91802 b7e24
            | exact resolve b7e24 b7e91802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e92266 : (σ y) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e92197
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e92197
            | exact resolve b7e92197 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e92197
          have b7e112704 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e76384
               have i₂ := b7e86717 (M.op y y)
               grind)
            | exact superpose b7e86717 b7e76384
            | exact resolve b7e76384 b7e86717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76384 b7e86717
          have b7e112731 : (σ x) = (σ y) := by grind
          clear b7e112704
          have b7e112756 : x = (σ y) := by
            first
            | (have i₁ := b7e112731
               have i₂ := b7e91802
               grind)
            | exact superpose b7e91802 b7e112731
            | exact resolve b7e112731 b7e91802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91802 b7e112731
          have b7e113794 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e112756
               grind)
            | exact superpose b7e112756 b7e23
            | exact resolve b7e23 b7e112756
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e113866 : x = (M.op x x) := by
            first
            | (have i₁ := b7e92266
               have i₂ := b7e112756
               grind)
            | exact superpose b7e112756 b7e92266
            | exact resolve b7e92266 b7e112756
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92266 b7e112756
          have b7e114007 : False := by grind
          exact b7e114007
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e4125 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 y y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e4284 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e4125
               have r₂ := b8e23
               grind)
            | exact resolve b8e4125 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4125
          have b8e4290 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e4284
               have r₂ := b8e24
               grind)
            | exact resolve b8e4284 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4284
          have b8e4293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e4290
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e4290
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e4290 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4290
          have b8e4294 : y = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e4293
          have b8e4296 : y = (M.op y x) := by
            first
            | (have r₁ := b8e4294
               have r₂ := b8e21
               grind)
            | exact resolve b8e4294 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4294
          have b8e4298 : False := by grind
          exact b8e4298

/-- `Equation4535`: `x ◇ (y ◇ z) = (y ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation4535 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4535 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4535.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e27
      have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e68 : False := by grind
      exact b0e68
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : x = y := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e25
          | exact resolve b3e25 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
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
          have b4e35 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e35 X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X1 X0
               have i₂ := b4e44 X0
               grind)
            | (have i₁ := b4e35 X0 y
               have i₂ := b4e44 y
               grind)
            | exact superpose b4e44 b4e35
            | exact resolve b4e35 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e79 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) X1) = (M.op X1 (M.op y X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 y X2 X0
               have i₂ := b4e44 X0
               grind)
            | (have i₁ := b4e13 X0 X0 X2 y
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e13
            | exact resolve b4e13 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e82 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e79 X0 X1 x
               have i₂ := b4e41 X1 x
               grind)
            | exact superpose b4e41 b4e79
            | exact resolve b4e79 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e79
          have b4e253 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e269 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e82 (σ y) X0
               have i₂ := b4e34 X0 y
               grind)
            | exact superpose b4e34 b4e82
            | exact resolve b4e82 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e270 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e77 (σ y) X0
               have i₂ := b4e34 X0 y
               grind)
            | exact superpose b4e34 b4e77
            | exact resolve b4e77 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e77
          have b4e300 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e253 X0
               have i₂ := b4e270 X0
               grind)
            | exact superpose b4e270 b4e253
            | exact resolve b4e253 b4e270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e253 b4e270
          have b4e318 : (σ y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e300 (σ x)
               grind)
            | exact superpose b4e300 b4e24
            | exact resolve b4e24 b4e300
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300
          have b4e340 : (σ y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e318
               have i₂ := b4e44 (σ x)
               grind)
            | exact superpose b4e44 b4e318
            | exact resolve b4e318 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e318
          have b4e1244 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e269 (σ x)
               grind)
            | exact superpose b4e269 b4e20
            | exact resolve b4e20 b4e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e269
          have b4e1255 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e1244
               have i₂ := b4e340
               grind)
            | exact superpose b4e340 b4e1244
            | exact resolve b4e1244 b4e340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e340 b4e1244
          have b4e1280 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e1255
               have i₂ := b4e44 x
               grind)
            | exact superpose b4e44 b4e1255
            | exact resolve b4e1255 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e1255
          have b4e1282 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e1280
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1280
            | exact resolve b4e1280 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1280
          have b4e1283 : False := by grind
          exact b4e1283
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y x X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e32 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e54 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e56 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = X0 ∨ (k X0 (M.op X1 X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e17 X0 (M.op X1 X3)
               have i₂ := b5e13 X0 X1 X2 X3
               grind)
            | (have i₁ := b5e17 (M.op X1 X2) X0
               have i₂ := b5e13 X0 X1 X2 X3
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 (M.op X1 X3) X0
               grind)
            | (have r₁ := b5e17 X0 (M.op X0 (M.op X0 X2))
               have r₂ := b5e13 X0 X0 X2 (M.op X0 X2)
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : x = y ∨ x = (k x y) := by grind
          clear b5e54
          have b5e59 : x = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e21
               grind)
            | exact resolve b5e58 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e67 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 X2 y
               have i₂ := b5e42 X0
               grind)
            | (have i₁ := b5e13 X0 y X2 X0
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e13
            | exact resolve b5e13 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X0 y X2
               have i₂ := b5e42 X0
               grind)
            | (have i₁ := b5e13 X0 y X0 x
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e13
            | exact resolve b5e13 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e68 X0 X1 X2
               have i₂ := b5e37 X1 X0
               grind)
            | exact superpose b5e37 b5e68
            | exact resolve b5e68 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e68
          have b5e78 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e67 X0 X1 X2
               have i₂ := b5e32 X1 X0
               grind)
            | exact superpose b5e32 b5e67
            | exact resolve b5e67 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e67
          have b5e126 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e26 X0 X1
               have i₂ := b5e18 (τ X0) X1
               grind)
            | exact superpose b5e18 b5e26
            | (have j1 := b5e18 (τ X0) X1
               grind)
            | exact resolve b5e26 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e648 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e78 (σ X0) X1 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e78
            | exact resolve b5e78 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3858 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X3) ≠ (M.op X2 (σ (k X0 X1))) ∨ (M.op (σ X0) X3) = X2 ∨ (k X2 (M.op (σ X0) X3)) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e56 X2 (σ X0) (σ X1) X3
               have i₂ := b5e62 X0 X1
               grind)
            | exact superpose b5e62 b5e56
            | (have j0 := b5e56 X2 (σ X0) X2 X3
               have j1 := b5e62 X0 X1
               grind)
            | exact resolve b5e56 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e3860 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e77 (σ X0) X2 (σ X1)
               have i₂ := b5e62 X0 X1
               grind)
            | exact superpose b5e62 b5e77
            | (have j1 := b5e62 X0 X1
               grind)
            | exact resolve b5e77 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e9605 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e126 (σ X0) X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e126
            | exact resolve b5e126 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e126
          have b5e9683 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e9605 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e9605
            | (have j0 := b5e9605 X0 X1
               grind)
            | exact resolve b5e9605 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9605
          have b5e16833 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op X1 (σ x)) ∨ (M.op (σ x) X0) = X1 ∨ (k X1 (M.op (σ x) X0)) = X1 ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b5e3858 x y X1 X0
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e3858
            | (have j0 := b5e3858 x y X1 X0
               grind)
            | exact resolve b5e3858 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3858
          have b5e16900 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op X1 (σ x)) ∨ (M.op (σ x) X0) = X1 ∨ (k X1 (M.op (σ x) X0)) = X1 ∨ (σ x) = (σ y) := by
            intro X0 X1
            first
            | (have j0 := b5e16833 X0 X1
               grind)
            | (have r₁ := b5e16833 X0 X1
               have r₂ := b5e24
               grind)
            | exact resolve b5e16833 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16833
          have b5e16934 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op X1 (σ x)) ∨ (M.op (σ x) X0) = X1 ∨ (k X1 (M.op (σ x) X0)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e16900 X0 X1
               grind)
            | (have r₁ := b5e16900 X0 X1
               have r₂ := b5e23
               grind)
            | exact resolve b5e16900 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16900
          have b5e37909 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
            first
            | (have j0 := b5e16934 (σ x) (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16934
          have b5e37910 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b5e37909
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e37909
            | exact resolve b5e37909 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37909
          have b5e37940 : (σ x) = (k (σ x) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e37910
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e37910
            | exact resolve b5e37910 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37910
          have b5e37953 : (σ x) = (σ (k x (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e37940
               have i₂ := b5e19 x (M.op x x)
               grind)
            | exact superpose b5e19 b5e37940
            | exact resolve b5e37940 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37940
          have b5e45568 : (σ x) = (σ (M.op x (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e9683 x (M.op x x)
               have i₂ := b5e37953
               grind)
            | exact superpose b5e37953 b5e9683
            | (have j0 := b5e9683 x (M.op x x)
               grind)
            | exact resolve b5e9683 b5e37953
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9683 b5e37953
          have b5e45673 : (σ (M.op x y)) = (σ x) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e45568
               have i₂ := b5e78 x x x
               grind)
            | exact superpose b5e78 b5e45568
            | exact resolve b5e45568 b5e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78 b5e45568
          have b5e45677 : (σ x) = (σ (M.op y x)) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e45673
               have i₂ := b5e42 x
               grind)
            | exact superpose b5e42 b5e45673
            | exact resolve b5e45673 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45673
          have b5e45680 : (σ x) = (σ y) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e45677
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e45677
            | exact resolve b5e45677 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45677
          have b5e45683 : (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e45680
               have r₂ := b5e23
               grind)
            | exact resolve b5e45680 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45680
          have b5e45686 : (M.op y x) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e45683
               have i₂ := b5e77 x x x
               grind)
            | exact superpose b5e77 b5e45683
            | exact resolve b5e45683 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45683
          have b5e45689 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b5e45686
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e45686
            | exact resolve b5e45686 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45686
          have b5e70912 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b5e14 (M.op x x)
               have i₂ := b5e45689
               grind)
            | exact superpose b5e45689 b5e14
            | exact resolve b5e14 b5e45689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45689
          have b5e71042 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b5e70912
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e70912
            | exact resolve b5e70912 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70912
          have b5e71043 : x = (M.op x x) ∨ y = (M.op x x) := by grind
          clear b5e71042
          have b5e71264 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ y = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b5e77 x X0 x
               have i₂ := b5e71043
               grind)
            | exact superpose b5e71043 b5e77
            | exact resolve b5e77 b5e71043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e71043
          have b5e71918 : y ≠ (M.op y x) ∨ y = (M.op x x) := by grind
          clear b5e71264
          have b5e71920 : y = (M.op x x) := by
            first
            | (have r₁ := b5e71918
               have r₂ := b5e22
               grind)
            | exact resolve b5e71918 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71918
          have b5e72433 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e648 x X0
               have i₂ := b5e71920
               grind)
            | exact superpose b5e71920 b5e648
            | exact resolve b5e648 b5e71920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e648
          have b5e295396 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e3860 x y X0
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e3860
            | (have j0 := b5e3860 x y x
               grind)
            | exact resolve b5e3860 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e3860
          have b5e295629 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e295396 X0
               grind)
            | (have r₁ := b5e295396 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e295396 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e295396
          have b5e295653 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b5e295629 X0
               grind)
            | (have r₁ := b5e295629 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e295629 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e295629
          have b5e295801 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e295653 (σ y)
               grind)
            | exact superpose b5e295653 b5e20
            | exact resolve b5e20 b5e295653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e295802 : (σ (M.op x x)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e30 x
               have i₂ := b5e295653 (σ x)
               grind)
            | exact superpose b5e295653 b5e30
            | exact resolve b5e30 b5e295653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e296059 : (M.op y y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e42 (σ x)
               have i₂ := b5e295653 y
               grind)
            | exact superpose b5e295653 b5e42
            | exact resolve b5e42 b5e295653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e295653
          have b5e296404 : (M.op y y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e295802
               have i₂ := b5e296059
               grind)
            | exact superpose b5e296059 b5e295802
            | exact resolve b5e295802 b5e296059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e295802 b5e296059
          have b5e296405 : (σ (M.op x y)) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e295801
               have i₂ := b5e72433 y
               grind)
            | exact superpose b5e72433 b5e295801
            | exact resolve b5e295801 b5e72433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72433 b5e295801
          have b5e296574 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b5e296404
               have i₂ := b5e71920
               grind)
            | exact superpose b5e71920 b5e296404
            | exact resolve b5e296404 b5e71920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71920 b5e296404
          have b5e296575 : (M.op y y) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b5e296405
               have i₂ := b5e42 x
               grind)
            | exact superpose b5e42 b5e296405
            | exact resolve b5e296405 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e296405
          have b5e296615 : (σ y) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e296575
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e296575
            | exact resolve b5e296575 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e296575
          have b5e296634 : False := by grind
          exact b5e296634
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : x = y := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
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
          have b7e37 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) X1 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2 x
               have i₂ := b7e13 X0 X1 X3 x
               grind)
            | (have i₁ := b7e13 (M.op X1 X2) X1 X2 X3
               have i₂ := b7e13 (M.op X1 X3) X1 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e51 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = X0 ∨ (k X0 (M.op X1 X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e17 X0 (M.op X1 X3)
               have i₂ := b7e13 X0 X1 X2 X3
               grind)
            | (have i₁ := b7e17 (M.op X1 X2) X0
               have i₂ := b7e13 X0 X1 X2 X3
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 (M.op X1 X3) X0
               grind)
            | (have r₁ := b7e17 X0 (M.op X0 (M.op X0 X2))
               have r₂ := b7e13 X0 X0 X2 (M.op X0 X2)
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e52 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e49
          have b7e53 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e52
               have r₂ := b7e23
               grind)
            | exact resolve b7e52 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e54 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e53
            | exact resolve b7e53 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e57 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e14
            | exact resolve b7e14 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : x = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e64 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e54
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e54 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e65 : (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e66 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e21
               grind)
            | exact resolve b7e65 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e69 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : x = (M.op x y) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e86 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 x X1 y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e13
            | exact resolve b7e13 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e99 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e32 X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e171 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 X2 (σ y)
               have i₂ := b7e99 X0
               grind)
            | (have i₁ := b7e13 X0 (σ y) X2 X0
               have i₂ := b7e99 X0
               grind)
            | exact superpose b7e99 b7e13
            | exact resolve b7e13 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e172 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op (σ y) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 (σ y) X2
               have i₂ := b7e99 X0
               grind)
            | (have i₁ := b7e13 X0 (σ y) X0 x
               have i₂ := b7e99 X0
               grind)
            | exact superpose b7e99 b7e13
            | exact resolve b7e13 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e189 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e172 X0 X1 X2
               have i₂ := b7e37 X1 X0
               grind)
            | exact superpose b7e37 b7e172
            | exact resolve b7e172 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e172
          have b7e190 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e171 X0 X1 X2
               have i₂ := b7e32 X1 X0
               grind)
            | exact superpose b7e32 b7e171
            | exact resolve b7e171 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e171
          have b7e232 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e86 X0 y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e86
            | exact resolve b7e86 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e233 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X2 (M.op (M.op X0 X1) x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e86 X2 (M.op X0 x)
               have i₂ := b7e13 x X0 x X1
               grind)
            | exact superpose b7e13 b7e86
            | exact resolve b7e86 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e251 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op x (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e37 X0 (M.op x x)
               have i₂ := b7e86 (σ y) x
               grind)
            | exact superpose b7e86 b7e37
            | exact resolve b7e37 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e253 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e251 X0
               have i₂ := b7e86 X0 (σ y)
               grind)
            | exact superpose b7e86 b7e251
            | exact resolve b7e251 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e251
          have b7e267 : ∀ X2 : G, (M.op X2 (σ y)) = (M.op x X2) := by
            intro X2
            first
            | (have i₁ := b7e233 x x X2
               have i₂ := b7e190 (M.op x x) X2 x
               grind)
            | exact superpose b7e190 b7e233
            | exact resolve b7e233 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e233
          have b7e316 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e40 X0 x X1 y
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e40
            | exact resolve b7e40 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e361 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e316 X0 x
               have i₂ := b7e190 x X0 x
               grind)
            | exact superpose b7e190 b7e316
            | exact resolve b7e316 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e316
          have b7e1080 : (σ (M.op x y)) ≠ (M.op (σ x) x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e361 (σ x)
               grind)
            | exact superpose b7e361 b7e20
            | exact resolve b7e20 b7e361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1081 : (σ (M.op y y)) = (M.op (σ y) x) := by
            first
            | (have i₁ := b7e30 y
               have i₂ := b7e361 (σ y)
               grind)
            | exact superpose b7e361 b7e30
            | exact resolve b7e30 b7e361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1085 : (σ (M.op y y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e1081
               have i₂ := b7e99 x
               grind)
            | exact superpose b7e99 b7e1081
            | exact resolve b7e1081 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1081
          have b7e1086 : (σ (M.op x y)) ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b7e1080
               have i₂ := b7e232 (σ x)
               grind)
            | exact superpose b7e232 b7e1080
            | exact resolve b7e1080 b7e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e232 b7e1080
          have b7e1102 : (M.op x x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e1085
               have i₂ := b7e267 x
               grind)
            | (have i₁ := b7e1085
               have i₂ := b7e267 (σ y)
               grind)
            | exact superpose b7e267 b7e1085
            | exact resolve b7e1085 b7e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1085
          have b7e1103 : (σ x) ≠ (M.op x (σ x)) := by
            first
            | (have i₁ := b7e1086
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e1086
            | exact resolve b7e1086 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66 b7e1086
          have b7e3455 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e51 X0 X0 x (M.op X0 X1)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e3456 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X0 ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e3455 X0 X1
               have i₂ := b7e190 X0 X0 X1
               grind)
            | exact superpose b7e190 b7e3455
            | (have j0 := b7e3455 X0 X1
               grind)
            | exact resolve b7e3455 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3455
          have b7e3519 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e3456 X0 X1
               have i₂ := b7e267 X0
               grind)
            | (have i₁ := b7e3456 x X1
               have i₂ := b7e267 (σ y)
               grind)
            | exact superpose b7e267 b7e3456
            | (have j0 := b7e3456 X0 X1
               grind)
            | exact resolve b7e3456 b7e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3456
          have b7e3572 : ∀ X0 : G, (k X0 (M.op X0 (σ y))) = X0 ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e3519 X0 x
               have i₂ := b7e190 X0 X0 x
               grind)
            | exact superpose b7e190 b7e3519
            | (have j0 := b7e3519 X0 x
               grind)
            | exact resolve b7e3519 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3519
          have b7e3596 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e3572 X0
               have i₂ := b7e267 X0
               grind)
            | (have i₁ := b7e3572 x
               have i₂ := b7e267 (σ y)
               grind)
            | exact superpose b7e267 b7e3572
            | (have j0 := b7e3572 X0
               grind)
            | exact resolve b7e3572 b7e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3572
          have b7e4077 : (M.op y y) = (τ (M.op x x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e1102
               grind)
            | exact superpose b7e1102 b7e14
            | exact resolve b7e14 b7e1102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e4080 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op x x) (M.op x x)) := by
            first
            | (have i₁ := b7e30 (M.op y y)
               have i₂ := b7e1102
               grind)
            | exact superpose b7e1102 b7e30
            | exact resolve b7e30 b7e1102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e1102
          have b7e4089 : (σ (M.op (M.op y y) (M.op y y))) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b7e4080
               have i₂ := b7e86 (M.op x x) x
               grind)
            | exact superpose b7e86 b7e4080
            | exact resolve b7e4080 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4080
          have b7e4094 : (M.op x x) = (σ (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b7e4089
               have i₂ := b7e86 x x
               grind)
            | exact superpose b7e86 b7e4089
            | exact resolve b7e4089 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86 b7e4089
          have b7e4099 : (M.op x x) = (σ (M.op (M.op y y) (σ y))) := by
            first
            | (have i₁ := b7e4094
               have i₂ := b7e190 y (M.op y y) y
               grind)
            | exact superpose b7e190 b7e4094
            | exact resolve b7e4094 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4094
          have b7e4100 : (M.op x x) = (σ (M.op (σ y) (M.op y y))) := by
            first
            | (have i₁ := b7e4099
               have i₂ := b7e99 (M.op y y)
               grind)
            | exact superpose b7e99 b7e4099
            | exact resolve b7e4099 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4099
          have b7e4101 : (M.op x x) = (σ (M.op x (M.op y y))) := by
            first
            | (have i₁ := b7e4100
               have i₂ := b7e253 (M.op y y)
               grind)
            | exact superpose b7e253 b7e4100
            | exact resolve b7e4100 b7e253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4100
          have b7e4102 : (M.op x x) = (σ (M.op x (σ y))) := by
            first
            | (have i₁ := b7e4101
               have i₂ := b7e190 y x y
               grind)
            | exact superpose b7e190 b7e4101
            | exact resolve b7e4101 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4101
          have b7e4103 : (M.op x x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e4102
               have i₂ := b7e267 x
               grind)
            | (have i₁ := b7e4102
               have i₂ := b7e267 (σ y)
               grind)
            | exact superpose b7e267 b7e4102
            | exact resolve b7e4102 b7e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4102
          have b7e4173 : (M.op x x) = (τ (M.op x x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e4103
               grind)
            | exact superpose b7e4103 b7e14
            | exact resolve b7e14 b7e4103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e4190 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e4173
               have i₂ := b7e4077
               grind)
            | exact superpose b7e4077 b7e4173
            | exact resolve b7e4173 b7e4077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4173
          have b7e4236 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e4103
               have i₂ := b7e4190
               grind)
            | exact superpose b7e4190 b7e4103
            | exact resolve b7e4103 b7e4190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4103
          have b7e4237 : (M.op y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b7e4077
               have i₂ := b7e4190
               grind)
            | exact superpose b7e4190 b7e4077
            | exact resolve b7e4077 b7e4190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6737 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x (σ X0)))) ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e80 X0 (M.op x (σ X0))
               have i₂ := b7e3596 (σ X0)
               grind)
            | exact superpose b7e3596 b7e80
            | (have j1 := b7e3596 (σ X0)
               grind)
            | exact resolve b7e80 b7e3596
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e3596
          have b7e6742 : ∀ X0 : G, (k X0 (τ (M.op x (σ X0)))) = X0 ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e6737 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e6737
            | (have j0 := b7e6737 X0
               grind)
            | exact resolve b7e6737 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6737
          have b7e62859 : y = (k y (τ (M.op x x))) ∨ (σ y) = (M.op x x) := by
            first
            | (have i₁ := b7e6742 y
               have i₂ := b7e361 x
               grind)
            | exact superpose b7e361 b7e6742
            | exact resolve b7e6742 b7e361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e361 b7e6742
          have b7e62911 : y = (k y (M.op y y)) ∨ (σ y) = (M.op x x) := by
            first
            | (have i₁ := b7e62859
               have i₂ := b7e4077
               grind)
            | exact superpose b7e4077 b7e62859
            | exact resolve b7e62859 b7e4077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4077 b7e62859
          have b7e62945 : y = (k y (M.op y y)) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e62911
               have i₂ := b7e4190
               grind)
            | exact superpose b7e4190 b7e62911
            | exact resolve b7e62911 b7e4190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62911
          have b7e63046 : y = (M.op y (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 y (M.op y y)
               have i₂ := b7e62945
               grind)
            | exact superpose b7e62945 b7e18
            | (have j0 := b7e18 (M.op y y) y
               grind)
            | exact resolve b7e18 b7e62945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62945
          have b7e63055 : y = (M.op y (σ y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e63046
               have i₂ := b7e190 y y y
               grind)
            | exact superpose b7e190 b7e63046
            | exact resolve b7e63046 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e190 b7e63046
          have b7e63058 : y = (M.op x y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e63055
               have i₂ := b7e267 y
               grind)
            | exact superpose b7e267 b7e63055
            | exact resolve b7e63055 b7e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63055
          have b7e63061 : x = y ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e63058
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e63058
            | exact resolve b7e63058 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63058
          have b7e63065 : (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have r₁ := b7e63061
               have r₂ := b7e21
               grind)
            | exact resolve b7e63061 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63061
          have b7e63068 : (M.op y y) = (M.op (σ y) y) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e63065
               have i₂ := b7e189 y y y
               grind)
            | exact superpose b7e189 b7e63065
            | exact resolve b7e63065 b7e189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e189 b7e63065
          have b7e63070 : (M.op y y) = (M.op y (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e63068
               have i₂ := b7e99 y
               grind)
            | exact superpose b7e99 b7e63068
            | exact resolve b7e63068 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99 b7e63068
          have b7e63072 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e63070
               have i₂ := b7e267 y
               grind)
            | exact superpose b7e267 b7e63070
            | exact resolve b7e63070 b7e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e267 b7e63070
          have b7e63074 : (σ y) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e63072
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e63072
            | exact resolve b7e63072 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63072
          have b7e110344 : (σ y) = (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e4237
               have i₂ := b7e63074
               grind)
            | exact superpose b7e63074 b7e4237
            | exact resolve b7e4237 b7e63074
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4237
          have b7e110449 : y ≠ (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b7e63074
          have b7e110514 : y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e110344
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e110344
            | exact resolve b7e110344 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110344
          have b7e110527 : x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b7e110514
               have r₂ := b7e110449
               grind)
            | exact resolve b7e110514 b7e110449
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110449 b7e110514
          have b7e111988 : y = (M.op y y) ∨ x = (σ x) := by
            first
            | (have i₁ := b7e4236
               have i₂ := b7e110527
               grind)
            | exact superpose b7e110527 b7e4236
            | exact resolve b7e4236 b7e110527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e112210 : x = (σ x) ∨ y = (σ y) := by
            first
            | (have i₁ := b7e4236
               have i₂ := b7e111988
               grind)
            | exact superpose b7e111988 b7e4236
            | exact resolve b7e4236 b7e111988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111988
          have b7e113044 : x ≠ (M.op x x) ∨ y = (σ y) := by
            first
            | (have i₁ := b7e1103
               have i₂ := b7e112210
               grind)
            | exact superpose b7e112210 b7e1103
            | exact resolve b7e1103 b7e112210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1103 b7e112210
          have b7e113166 : x ≠ (M.op y y) ∨ y = (σ y) := by
            first
            | (have i₁ := b7e113044
               have i₂ := b7e4190
               grind)
            | exact superpose b7e4190 b7e113044
            | exact resolve b7e113044 b7e4190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4190 b7e113044
          have b7e115596 : x ≠ x ∨ y = (σ y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e113166
               have i₂ := b7e110527
               grind)
            | exact superpose b7e110527 b7e113166
            | (have r₁ := b7e113166
               have r₂ := b7e110527
               grind)
            | exact resolve b7e113166 b7e110527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110527 b7e113166
          have b7e115598 : y = (M.op y y) ∨ y = (σ y) := by grind
          clear b7e115596
          have b7e116076 : y = (σ y) ∨ y = (σ y) := by
            first
            | (have i₁ := b7e4236
               have i₂ := b7e115598
               grind)
            | exact superpose b7e115598 b7e4236
            | exact resolve b7e4236 b7e115598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115598
          have b7e116195 : y = (σ y) := by grind
          clear b7e116076
          have b7e116683 : y = (M.op y (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e116195
               grind)
            | exact superpose b7e116195 b7e24
            | exact resolve b7e24 b7e116195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e116698 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e253 X0
               have i₂ := b7e116195
               grind)
            | exact superpose b7e116195 b7e253
            | exact resolve b7e253 b7e116195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e253 b7e116195
          have b7e120962 : x = (M.op y y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e116698 y
               grind)
            | exact superpose b7e116698 b7e71
            | exact resolve b7e71 b7e116698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e116698
          have b7e124178 : x = (σ x) := by
            first
            | (have i₁ := b7e4236
               have i₂ := b7e120962
               grind)
            | exact superpose b7e120962 b7e4236
            | exact resolve b7e4236 b7e120962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4236 b7e120962
          have b7e126760 : y = (M.op y x) := by
            first
            | (have i₁ := b7e116683
               have i₂ := b7e124178
               grind)
            | exact superpose b7e124178 b7e116683
            | exact resolve b7e116683 b7e124178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e116683 b7e124178
          have b7e126906 : False := by grind
          exact b7e126906
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e1613 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 x y
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1684 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1613
               have r₂ := b8e24
               grind)
            | exact resolve b8e1613 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1613
          have b8e1693 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1684
               have r₂ := b8e23
               grind)
            | exact resolve b8e1684 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1684
          have b8e1698 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1693
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1693
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1693
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1693
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1693 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1693
          have b8e1699 : y = (M.op y x) ∨ x = y := by grind
          clear b8e1698
          have b8e1700 : x = y := by
            first
            | (have r₁ := b8e1699
               have r₂ := b8e22
               grind)
            | exact resolve b8e1699 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1699
          have b8e1701 : False := by grind
          exact b8e1701

/-- `Equation4541`: `x ◇ (y ◇ z) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation4541 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4541 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4541.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e27
      have b0e60 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e62 : False := by grind
      exact b0e62
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : x = y := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e25
          | exact resolve b3e25 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op x (M.op X1 X0)) = (M.op x (M.op X0 (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (M.op X1 X0)
               have i₂ := b4e13 X0 y X1
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X1 x)) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 y) X1 x
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X1 x)) = (M.op X0 (M.op X1 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 X0 X1
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op y (M.op (M.op X1 x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X0 X1
               have i₂ := b4e13 y (M.op X1 x) X0
               grind)
            | exact superpose b4e13 b4e40
            | exact resolve b4e40 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op y (M.op x (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 X1
               have i₂ := b4e13 x X0 X1
               grind)
            | exact superpose b4e13 b4e41
            | exact resolve b4e41 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e81 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ X0) X1 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e85 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op X1 (σ x))) = (M.op (M.op (σ x) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 (σ y)) X1 (σ x)
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e86 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op X1 (σ x))) = (M.op X0 (M.op X1 (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b4e85 X0 X1
               have i₂ := b4e13 X0 X1 (σ x)
               grind)
            | exact superpose b4e13 b4e85
            | exact resolve b4e85 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85
          have b4e87 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (σ y) (M.op (M.op X1 (σ x)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e86 X0 X1
               have i₂ := b4e13 (σ y) (M.op X1 (σ x)) X0
               grind)
            | exact superpose b4e13 b4e86
            | exact resolve b4e86 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86
          have b4e88 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (σ y) (M.op (σ x) (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e87 X0 X1
               have i₂ := b4e13 (σ x) X0 X1
               grind)
            | exact superpose b4e13 b4e87
            | exact resolve b4e87 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87
          have b4e286 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e54 x y
               grind)
            | exact superpose b4e54 b4e20
            | (have j1 := b4e54 x y
               grind)
            | exact resolve b4e20 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e296 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e286
               have r₂ := b4e23
               grind)
            | exact resolve b4e286 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286
          have b4e399 : ∀ X0 : G, (M.op X0 (M.op y x)) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e42 X0 y
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e42
            | exact resolve b4e42 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e400 : ∀ X0 X1 : G, (M.op y (M.op x (M.op X0 X1))) = (M.op X1 (M.op (M.op y X0) x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e42 X1 (M.op y X0)
               have i₂ := b4e38 X1 X0
               grind)
            | exact superpose b4e38 b4e42
            | exact resolve b4e42 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e426 : ∀ X0 X1 : G, (M.op y (M.op x (M.op X0 X1))) = (M.op X1 (M.op X0 (M.op x y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e400 X0 X1
               have i₂ := b4e13 X0 x y
               grind)
            | exact superpose b4e13 b4e400
            | exact resolve b4e400 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e400
          have b4e427 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e399 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e399
            | exact resolve b4e399 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e399
          have b4e445 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X1 (M.op X0 (M.op x y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e426 X0 X1
               have i₂ := b4e42 X0 X1
               grind)
            | exact superpose b4e42 b4e426
            | exact resolve b4e426 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e426
          have b4e502 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X0 X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b4e42 X0 X1
               have i₂ := b4e427 (M.op X0 X1)
               grind)
            | exact superpose b4e427 b4e42
            | exact resolve b4e42 b4e427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e523 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X1 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e502 X0 X1
               have i₂ := b4e13 X1 x X0
               grind)
            | exact superpose b4e13 b4e502
            | exact resolve b4e502 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e502
          have b4e865 : (M.op (σ (M.op x x)) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e81 x (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e81
            | exact resolve b4e81 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e889 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b4e865
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e865
            | exact resolve b4e865 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e865
          have b4e960 : ∀ X0 : G, (M.op X0 (M.op y x)) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e445 y X0
               have i₂ := b4e427 y
               grind)
            | exact superpose b4e427 b4e445
            | exact resolve b4e445 b4e427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e427 b4e445
          have b4e1003 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e960 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e960
            | exact resolve b4e960 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e960
          have b4e1102 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e523 y X0
               have i₂ := b4e1003 X0
               grind)
            | exact superpose b4e1003 b4e523
            | exact resolve b4e523 b4e1003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e523
          have b4e1180 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op x y) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op x y) X1 X0
               have i₂ := b4e1102 X0
               grind)
            | exact superpose b4e1102 b4e13
            | exact resolve b4e13 b4e1102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1189 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op y (M.op (M.op X1 X0) x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1180 X0 X1
               have i₂ := b4e13 y (M.op X1 X0) x
               grind)
            | exact superpose b4e13 b4e1180
            | exact resolve b4e1180 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1180
          have b4e1197 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op X1 X0) x) := by
            intro X0 X1
            first
            | (have i₁ := b4e1189 X0 X1
               have i₂ := b4e1003 (M.op X1 X0)
               grind)
            | exact superpose b4e1003 b4e1189
            | exact resolve b4e1189 b4e1003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1003 b4e1189
          have b4e1204 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op (M.op X0 x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e1197 X0 X1
               have i₂ := b4e13 X0 x X1
               grind)
            | exact superpose b4e13 b4e1197
            | exact resolve b4e1197 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1197
          have b4e1209 : ∀ X0 X1 : G, (M.op x (M.op X1 X0)) = (M.op X0 (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1204 X0 X1
               have i₂ := b4e13 x X1 X0
               grind)
            | exact superpose b4e13 b4e1204
            | exact resolve b4e1204 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1204
          have b4e1832 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ x))) = (M.op (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b4e88 X0 (σ y)
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e88
            | exact resolve b4e88 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1886 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b4e1832 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1832
            | exact resolve b4e1832 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1832
          have b4e2998 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e1102 X0
               have i₂ := b4e1209 X0 y
               grind)
            | (have i₁ := b4e1102 x
               have i₂ := b4e1209 y x
               grind)
            | exact superpose b4e1209 b4e1102
            | exact resolve b4e1102 b4e1209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1102 b4e1209
          have b4e3218 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e32 y
               have i₂ := b4e2998 y
               grind)
            | exact superpose b4e2998 b4e32
            | exact resolve b4e32 b4e2998
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e2998
          have b4e3258 : x = (M.op x y) := by
            first
            | (have i₁ := b4e3218
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e3218
            | exact resolve b4e3218 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3218
          have b4e3342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e296
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e296
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e296
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e296
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e296 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e296
          have b4e3343 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b4e3342
          have b4e3344 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e3343
               have r₂ := b4e21
               grind)
            | exact resolve b4e3343 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3343
          have b4e3345 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e3344
               have i₂ := b4e3258
               grind)
            | exact superpose b4e3258 b4e3344
            | exact resolve b4e3344 b4e3258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3258 b4e3344
          have b4e3346 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e3345
               have r₂ := b4e21
               grind)
            | exact resolve b4e3345 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3345
          have b4e3744 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e33 (σ x)
               have i₂ := b4e3346
               grind)
            | exact superpose b4e3346 b4e33
            | exact resolve b4e33 b4e3346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e3752 : (M.op (σ x) (M.op (σ y) (σ x))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e88 (σ x) (σ y)
               have i₂ := b4e3346
               grind)
            | exact superpose b4e3346 b4e88
            | exact resolve b4e88 b4e3346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88
          have b4e3757 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b4e3752
               have i₂ := b4e1886 (σ y)
               grind)
            | exact superpose b4e1886 b4e3752
            | exact resolve b4e3752 b4e1886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1886 b4e3752
          have b4e3761 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e3744
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e3744
            | exact resolve b4e3744 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e3744
          have b4e3765 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b4e3757
               have i₂ := b4e81 x (σ y)
               grind)
            | exact superpose b4e81 b4e3757
            | exact resolve b4e3757 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81 b4e3757
          have b4e3768 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e3761
               have i₂ := b4e3346
               grind)
            | exact superpose b4e3346 b4e3761
            | exact resolve b4e3761 b4e3346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3346 b4e3761
          have b4e3770 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e3765
               have i₂ := b4e889
               grind)
            | exact superpose b4e889 b4e3765
            | exact resolve b4e3765 b4e889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e889 b4e3765
          have b4e3773 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e3770
               have i₂ := b4e3768
               grind)
            | exact superpose b4e3768 b4e3770
            | exact resolve b4e3770 b4e3768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3768 b4e3770
          have b4e3775 : (σ x) = (σ y) := by
            first
            | (have i₁ := b4e3773
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e3773
            | exact resolve b4e3773 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3773
          have b4e3777 : False := by grind
          exact b4e3777
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e42 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e45 : x = y ∨ x = (k x y) := by grind
          clear b5e42
          have b5e46 : x = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e243 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e8833 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e243 y x
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e243
            | (have j0 := b5e243 y x
               grind)
            | exact resolve b5e243 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e243
          have b5e8836 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e8833
          have b5e8839 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e8836
               have r₂ := b5e24
               grind)
            | exact resolve b5e8836 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8836
          have b5e8843 : False := by grind
          exact b5e8843
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : x = y := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e44 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e44
          have b7e47 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e47
            | exact resolve b7e47 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e51 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e14
            | exact resolve b7e14 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e52 : x = (k x y) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e51
            | exact resolve b7e51 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e63 : x = (M.op y x) ∨ x = y := by grind
          clear b7e62
          have b7e65 : x = y := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e22
               grind)
            | exact resolve b7e63 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e67 : False := by grind
          exact b7e67
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e206 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e57 x y
               grind)
            | exact superpose b8e57 b8e20
            | (have j1 := b8e57 x y
               grind)
            | exact resolve b8e20 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e215 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e206
               have r₂ := b8e23
               grind)
            | exact resolve b8e206 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e206
          have b8e475 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e215
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e215
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e215
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e215
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e215 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e476 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e475
          have b8e477 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e476
               have r₂ := b8e21
               grind)
            | exact resolve b8e476 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e476
          have b8e479 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e477
               grind)
            | exact superpose b8e477 b8e20
            | exact resolve b8e20 b8e477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e484 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e477
               grind)
            | exact superpose b8e477 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e477
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e477
               grind)
            | exact resolve b8e17 b8e477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e477
          have b8e486 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e484
          have b8e487 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e486
               have r₂ := b8e23
               grind)
            | exact resolve b8e486 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e486
          have b8e490 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e487
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e487
            | exact resolve b8e487 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e487
          have b8e1009 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e490
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e490
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e490 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e490
          have b8e1029 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e1009
          have b8e1046 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e1029
               have r₂ := b8e479
               grind)
            | exact resolve b8e1029 b8e479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e479 b8e1029
          have b8e1047 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1046
               have r₂ := b8e21
               grind)
            | exact resolve b8e1046 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1046
          have b8e1627 : y ≠ y ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e1047
               grind)
            | exact superpose b8e1047 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1047
               grind)
            | exact resolve b8e17 b8e1047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1636 : x = y ∨ y = (k y x) := by grind
          clear b8e1627
          have b8e1641 : y = (k y x) := by
            first
            | (have r₁ := b8e1636
               have r₂ := b8e21
               grind)
            | exact resolve b8e1636 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1636
          have b8e2132 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e215
               have i₂ := b8e1641
               grind)
            | exact superpose b8e1641 b8e215
            | exact resolve b8e215 b8e1641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e215 b8e1641
          have b8e2136 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e2132
               have i₂ := b8e1047
               grind)
            | exact superpose b8e1047 b8e2132
            | exact resolve b8e2132 b8e1047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2132
          have b8e2137 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e2136
          have b8e2843 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2137
               grind)
            | exact superpose b8e2137 b8e20
            | exact resolve b8e20 b8e2137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2137
          have b8e2868 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e2843
               have i₂ := b8e1047
               grind)
            | exact superpose b8e1047 b8e2843
            | exact resolve b8e2843 b8e1047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1047 b8e2843
          have b8e2869 : False := by grind
          exact b8e2869

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation455 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law455 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op X0 X0) X0
           have i₂ := b0e11 (M.op X0 X0) X0 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e30 X0
           have i₂ := b0e33 (σ y) (σ y)
           grind)
        | exact superpose b0e33 b0e30
        | exact resolve b0e30 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e38 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e33 y y
           grind)
        | exact superpose b0e33 b0e29
        | exact resolve b0e29 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e33
      have b0e51 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e37 (σ x)
           grind)
        | exact superpose b0e37 b0e18
        | exact resolve b0e18 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e58 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e51
           have i₂ := b0e38 x
           grind)
        | exact superpose b0e38 b0e51
        | exact resolve b0e51 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e51
      have b0e59 : False := by grind
      exact b0e59
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b1e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b1e26 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e67 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e17 (σ y) X0
             grind)
          | exact superpose b1e17 b1e21
          | (have j1 := b1e17 X0 X0
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 X0 (σ y)
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 (σ y) x
             grind)
          | exact resolve b1e21 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e78 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e67 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e120 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e27 X0 y
             have i₂ := b1e26 (τ X0)
             grind)
          | exact superpose b1e26 b1e27
          | exact resolve b1e27 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e27
        have b1e128 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e120 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e120
          | exact resolve b1e120 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e120
        have b1e293 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e128 (σ y)
             have i₂ := b1e78 (σ y)
             grind)
          | exact superpose b1e78 b1e128
          | (have j1 := b1e78 (σ y)
             grind)
          | exact resolve b1e128 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78 b1e128
        have b1e298 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e293
        have b1e302 : False := by grind
        exact b1e302
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b2e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
        have b2e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
        have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e64 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ y) X0
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) x
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e75 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e64 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e91 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 y
             have i₂ := b2e24 (τ X0)
             grind)
          | exact superpose b2e24 b2e25
          | exact resolve b2e25 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e25
        have b2e98 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e91 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e91
          | exact resolve b2e91 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e234 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e98 (σ y)
             have i₂ := b2e75 (σ y)
             grind)
          | exact superpose b2e75 b2e98
          | (have j1 := b2e75 (σ y)
             grind)
          | exact resolve b2e98 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75 b2e98
        have b2e237 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e234
        have b2e241 : False := by grind
        exact b2e241
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b3e25 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e30 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e25 (σ X0)
             grind)
          | exact superpose b3e25 b3e18
          | exact resolve b3e18 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e34 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e33 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e33
          | exact resolve b3e33 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e41 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 (M.op X0 X0) X0
             have i₂ := b3e12 (M.op X0 X0) X0 X0
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e16 (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) X0
             grind)
          | (have r₁ := b3e16 (σ y) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have j0 := b3e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e242 : (σ y) = (M.op (σ y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e34 (σ y)
             have i₂ := b3e57 y
             grind)
          | exact superpose b3e57 b3e34
          | (have j1 := b3e57 y
             grind)
          | exact resolve b3e34 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e57
        have b3e251 : (σ y) = (M.op (σ y) y) := by
          first
          | (have r₁ := b3e242
             have r₂ := b3e20
             grind)
          | exact resolve b3e242 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e242
        have b3e257 : ∀ X0 : G, (M.op X0 (M.op y (M.op (σ y) (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y (σ y)
             have i₂ := b3e251
             grind)
          | exact superpose b3e251 b3e12
          | exact resolve b3e12 b3e251
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e251
        have b3e258 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e257 X0
             have i₂ := b3e41 (σ y) y
             grind)
          | exact superpose b3e41 b3e257
          | exact resolve b3e257 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e257
        have b3e319 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e258 y
             grind)
          | exact superpose b3e258 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e258 y
             grind)
          | exact resolve b3e20 b3e258
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e258
        have b3e320 : False := by grind
        exact b3e320
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e33 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 X0) X0
               have i₂ := b4e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e37 x x
               grind)
            | exact superpose b4e37 b4e33
            | exact resolve b4e33 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e37
          have b4e48 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b4e50 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e17 x X0
               have i₂ := b4e42 x
               grind)
            | exact superpose b4e42 b4e17
            | (have j0 := b4e17 x X0
               grind)
            | (have r₁ := b4e17 x x
               have r₂ := b4e42 x
               grind)
            | exact resolve b4e17 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k x X0) = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e50 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e53 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b4e48 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e231 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 x X0
               have i₂ := b4e53 (σ X0)
               grind)
            | exact superpose b4e53 b4e19
            | (have j1 := b4e53 (σ X0)
               grind)
            | exact resolve b4e19 b4e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e4512 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e231 y
               grind)
            | exact superpose b4e231 b4e23
            | (have j1 := b4e231 y
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e231 y
               grind)
            | exact resolve b4e23 b4e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e231
          have b4e4536 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b4e4512
          have b4e4558 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e4536
               grind)
            | exact superpose b4e4536 b4e20
            | exact resolve b4e20 b4e4536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4536
          have b4e4680 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e4558
               have i₂ := b4e51 y
               grind)
            | exact superpose b4e51 b4e4558
            | (have j1 := b4e51 y
               grind)
            | exact resolve b4e4558 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e4558
          have b4e4696 : y = (M.op y y) := by grind
          clear b4e4680
          have b4e4699 : False := by grind
          exact b4e4699
        · have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b5e25 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
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
          have b5e26 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b5e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25
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
          have b5e30 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 x
               have i₂ := b5e26 (τ X0)
               grind)
            | exact superpose b5e26 b5e27
            | exact resolve b5e27 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e27
          have b5e34 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e30
            | exact resolve b5e30 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e69 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) x
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e74 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e69 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e204 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e34 (σ x)
               have i₂ := b5e74 (σ x)
               grind)
            | exact superpose b5e74 b5e34
            | (have j1 := b5e74 (σ x)
               grind)
            | exact resolve b5e34 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e74
          have b5e207 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e204
          have b5e211 : False := by grind
          exact b5e211
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b6e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
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
        have b6e24 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e28 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e24 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e31 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e28 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e32 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X2 X0
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X1
             have j1 := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e83 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e69 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e677 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e83 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e678 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e677 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e677
        have b6e679 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e678 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e678
        have b6e986 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e32 y
             have i₂ := b6e679 y
             grind)
          | exact superpose b6e679 b6e32
          | (have j1 := b6e679 y
             grind)
          | exact resolve b6e32 b6e679
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e679
        have b6e988 : y = (M.op y y) := by grind
        clear b6e986
        have b6e1018 : False := by grind
        exact b6e1018
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
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
          have b7e26 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b7e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25
          have b7e30 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 x
               have i₂ := b7e26 (σ X0)
               grind)
            | exact superpose b7e26 b7e19
            | exact resolve b7e19 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e33 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b7e14 (k X0 x)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e14
            | exact resolve b7e14 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e34 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e40 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0) X0
               have i₂ := b7e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e17 (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) X0
               grind)
            | (have r₁ := b7e17 (σ x) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b7e45 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e221 : (σ x) = (M.op (σ x) x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34 (σ x)
               have i₂ := b7e48 x
               grind)
            | exact superpose b7e48 b7e34
            | (have j1 := b7e48 x
               grind)
            | exact resolve b7e34 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e48
          have b7e230 : (σ x) = (M.op (σ x) x) := by
            first
            | (have r₁ := b7e221
               have r₂ := b7e22
               grind)
            | exact resolve b7e221 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e221
          have b7e236 : ∀ X0 : G, (M.op X0 (M.op x (M.op (σ x) (σ x)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x (σ x)
               have i₂ := b7e230
               grind)
            | exact superpose b7e230 b7e13
            | exact resolve b7e13 b7e230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e230
          have b7e237 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e236 X0
               have i₂ := b7e40 (σ x) x
               grind)
            | exact superpose b7e40 b7e236
            | exact resolve b7e236 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e236
          have b7e270 : x ≠ x := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e237 x
               grind)
            | exact superpose b7e237 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e237 x
               grind)
            | exact resolve b7e22 b7e237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e237
          have b7e271 : False := by grind
          exact b7e271
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0) X0
               have i₂ := b8e13 (M.op X0 X0) X0 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e57 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e29 X0 X1
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e29
            | (have j1 := b8e18 X2 X2
               grind)
            | exact resolve b8e29 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29
          have b8e60 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
          have b8e65 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e60 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e219 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 y X0
               have i₂ := b8e65 (σ X0)
               grind)
            | exact superpose b8e65 b8e19
            | (have j1 := b8e65 (σ X0)
               grind)
            | exact resolve b8e19 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e5395 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e219 x
               grind)
            | exact superpose b8e219 b8e20
            | (have j1 := b8e219 x
               grind)
            | exact resolve b8e20 b8e219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219
          have b8e5516 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e5395
               have r₂ := b8e24
               grind)
            | exact resolve b8e5395 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5395
          have b8e6414 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 y) = X0 ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e5516
               have i₂ := b8e57 y X0 x
               grind)
            | exact superpose b8e57 b8e5516
            | (have j1 := b8e57 y X0 x
               grind)
            | exact resolve b8e5516 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57 b8e5516
          have b8e6433 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
            intro X0
            first
            | (have j0 := b8e6414 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6414
          have b8e6440 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b8e6433 X0
               grind)
            | (have r₁ := b8e6433 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e6433 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6433
          have b8e6557 : y ≠ y := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e6440 y
               grind)
            | exact superpose b8e6440 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e6440 y
               grind)
            | exact resolve b8e21 b8e6440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6440
          have b8e6558 : False := by grind
          exact b8e6558

/-- `Equation508`: `x = y ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pxy_pyx_Equation508 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law508 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law508.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y y) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ y)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e12 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
             have i₂ := b0e12 X0 (M.op X0 (M.op X2 X2)) X2
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X1 X1 (M.op X0 X0)
             have i₂ := b0e12 (M.op X0 X0) X1 X0
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b0e36 X0 X1 x
             have i₂ := b0e37 x X0
             grind)
          | exact superpose b0e37 b0e36
          | exact resolve b0e36 b0e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e41 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b0e37 x X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e37
          | exact resolve b0e37 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e42 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b0e37 y X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e37
          | exact resolve b0e37 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37
        have b0e87 : ∀ X0 : G, x = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b0e38 x X0
             have i₂ := b0e41 X0
             grind)
          | exact superpose b0e41 b0e38
          | exact resolve b0e38 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e88 : ∀ X0 : G, y = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b0e38 y X0
             have i₂ := b0e42 X0
             grind)
          | exact superpose b0e42 b0e38
          | exact resolve b0e38 b0e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38 b0e42
        have b0e97 : x = y := by
          first
          | (have i₁ := b0e87 x
             have i₂ := b0e88 x
             grind)
          | exact superpose b0e88 b0e87
          | exact resolve b0e87 b0e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e87 b0e88
        have b0e99 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e97
             grind)
          | exact superpose b0e97 b0e19
          | exact resolve b0e19 b0e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e97
        have b0e102 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e99
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e99
          | exact resolve b0e99 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e99
        have b0e103 : False := by grind
        exact b0e103
      · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b1e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e20
            | exact resolve b1e20 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 X1 (M.op X0 X0)
               have i₂ := b1e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e40 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b1e37 (σ y) X0
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e37
            | exact resolve b1e37 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e37
          have b1e82 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b1e25
               have i₂ := b1e40 (σ x)
               grind)
            | exact superpose b1e40 b1e25
            | (have r₁ := b1e25
               have r₂ := b1e40 (σ x)
               grind)
            | exact resolve b1e25 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e25 b1e40
          have b1e83 : False := by grind
          exact b1e83
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b2e21 : y = (M.op y y) := by grind
          have b2e24 : x ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 X1 (M.op X0 X0)
               have i₂ := b2e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e38 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e36 y X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e36
            | exact resolve b2e36 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36
          have b2e56 : x ≠ x := by
            first
            | (have i₁ := b2e24
               have i₂ := b2e38 x
               grind)
            | exact superpose b2e38 b2e24
            | (have r₁ := b2e24
               have r₂ := b2e38 x
               grind)
            | exact resolve b2e24 b2e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e38
          have b2e57 : False := by grind
          exact b2e57
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b3e21 : y = (M.op y y) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b3e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b3e13 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
               have i₂ := b3e13 X0 (M.op X0 (M.op X2 X2)) X2
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X1 X1 (M.op X0 X0)
               have i₂ := b3e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e35 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b3e33 X0 X1 x
               have i₂ := b3e34 x X0
               grind)
            | exact superpose b3e34 b3e33
            | exact resolve b3e33 b3e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33
          have b3e37 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b3e34 x X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e34
            | exact resolve b3e34 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e38 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b3e34 y X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e34
            | exact resolve b3e34 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e34
          have b3e88 : ∀ X0 : G, x = (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b3e35 x X0
               have i₂ := b3e37 X0
               grind)
            | exact superpose b3e37 b3e35
            | exact resolve b3e35 b3e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e37
          have b3e89 : ∀ X0 : G, y = (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b3e35 y X0
               have i₂ := b3e38 X0
               grind)
            | exact superpose b3e38 b3e35
            | exact resolve b3e35 b3e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e35 b3e38
          have b3e98 : x = y := by
            first
            | (have i₁ := b3e88 x
               have i₂ := b3e89 x
               grind)
            | exact superpose b3e89 b3e88
            | exact resolve b3e88 b3e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e88 b3e89
          have b3e102 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e23
               have i₂ := b3e98
               grind)
            | exact superpose b3e98 b3e23
            | exact resolve b3e23 b3e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e98
          have b3e104 : False := by grind
          exact b3e104
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e22 : y = (M.op y y) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b4e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b4e21
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e21
              | exact resolve b4e21 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e28 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
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
            have b4e29 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b4e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e28
            have b4e46 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e18 (σ x) (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e50 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b4e46
            have b4e53 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e50
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e50 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e50
            have b4e55 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b4e53
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e53
              | exact resolve b4e53 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e53
            have b4e56 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b4e55
                 have i₂ := b4e29 x
                 grind)
              | exact superpose b4e29 b4e55
              | exact resolve b4e55 b4e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e29 b4e55
            have b4e57 : False := by grind
            exact b4e57
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b5e22 : y = (M.op y y) := by grind
            have b5e26 : x ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X1 X1 (M.op X0 X0)
                 have i₂ := b5e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e35 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b5e33 y X0
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e33
              | exact resolve b5e33 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e33
            have b5e57 : x ≠ x := by
              first
              | (have i₁ := b5e26
                 have i₂ := b5e35 x
                 grind)
              | exact superpose b5e35 b5e26
              | (have r₁ := b5e26
                 have r₂ := b5e35 x
                 grind)
              | exact resolve b5e26 b5e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e35
            have b5e58 : False := by grind
            exact b5e58
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e25 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 X0 y
               grind)
            | (have r₁ := b6e16 X0 y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e28 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b6e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e25
          have b6e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 X0
               have i₂ := b6e18 (σ X1) (σ X0)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X0) (σ X0)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e353 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e59 y y
               grind)
            | exact superpose b6e59 b6e22
            | (have j1 := b6e59 y y
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e59 y x
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e59 y y
               grind)
            | exact resolve b6e22 b6e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e59
          have b6e388 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b6e353
          have b6e409 : (σ y) ≠ (σ (k y y)) := by
            first
            | (have r₁ := b6e388
               have r₂ := b6e22
               grind)
            | exact resolve b6e388 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e388
          have b6e428 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e409
               have i₂ := b6e28 y
               grind)
            | exact superpose b6e28 b6e409
            | exact resolve b6e409 b6e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28 b6e409
          have b6e429 : False := by grind
          exact b6e429
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : y = (M.op y y) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b7e17 X0 y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 X0 y
                 grind)
              | (have r₁ := b7e17 X0 y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e29 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b7e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e28
            have b7e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X1 X0
                 have i₂ := b7e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b7e19 b7e20
              | (have j1 := b7e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b7e20 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e288 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b7e23
                 have i₂ := b7e60 y y
                 grind)
              | exact superpose b7e60 b7e23
              | (have j1 := b7e60 y y
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e60 y x
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e60 y y
                 grind)
              | exact resolve b7e23 b7e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e60
            have b7e323 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b7e288
            have b7e344 : (σ y) ≠ (σ (k y y)) := by
              first
              | (have r₁ := b7e323
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e323 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e323
            have b7e363 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b7e344
                 have i₂ := b7e29 y
                 grind)
              | exact superpose b7e29 b7e344
              | exact resolve b7e344 b7e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e344
            have b7e364 : False := by grind
            exact b7e364
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b8e22 : y = (M.op y y) := by grind
            have b8e26 : x ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 X1 (M.op X0 X0)
                 have i₂ := b8e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e35 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b8e33 y X0
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e33
              | exact resolve b8e33 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33
            have b8e52 : x ≠ x := by
              first
              | (have i₁ := b8e26
                 have i₂ := b8e35 x
                 grind)
              | exact superpose b8e35 b8e26
              | (have r₁ := b8e26
                 have r₂ := b8e35 x
                 grind)
              | exact resolve b8e26 b8e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35
            have b8e53 : False := by grind
            exact b8e53
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e22 : y = (M.op y x) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b9e16 X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 X0 (σ y)
               grind)
            | (have r₁ := b9e16 X0 (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e27 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b9e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 y
               have i₂ := b9e27 (σ X0)
               grind)
            | exact superpose b9e27 b9e19
            | exact resolve b9e19 b9e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X1 X1 (M.op X0 X0)
               have i₂ := b9e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e39 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b9e36 (σ y) X0
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e36
            | exact resolve b9e36 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e36
          have b9e48 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b9e17 x y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x y
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e52 : y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
          clear b9e48
          have b9e54 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b9e52
               have r₂ := b9e21
               grind)
            | exact resolve b9e52 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e52
          have b9e81 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e39 (σ x)
               grind)
            | exact superpose b9e39 b9e20
            | exact resolve b9e20 b9e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e39
          have b9e210 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b9e32 x
               have i₂ := b9e54
               grind)
            | exact superpose b9e54 b9e32
            | exact resolve b9e32 b9e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32 b9e54
          have b9e221 : False := by grind
          exact b9e221
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b10e22 : y ≠ (M.op y y) := by grind
            have b10e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e14 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                 have i₂ := b10e14 X0 (M.op X0 (M.op X2 X2)) X2
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b10e14 X1 X1 (M.op X0 X0)
                 have i₂ := b10e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e37 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b10e35 X0 X1 x
                 have i₂ := b10e36 x X0
                 grind)
              | exact superpose b10e36 b10e35
              | exact resolve b10e35 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e35
            have b10e81 : y = (M.op x x) := by
              first
              | (have i₁ := b10e37 y x
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e37
              | exact resolve b10e37 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e37
            have b10e89 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b10e36 x X0
                 have i₂ := b10e81
                 grind)
              | exact superpose b10e81 b10e36
              | exact resolve b10e36 b10e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e36 b10e81
            have b10e144 : y ≠ y := by
              first
              | (have i₁ := b10e22
                 have i₂ := b10e89 y
                 grind)
              | exact superpose b10e89 b10e22
              | (have r₁ := b10e22
                 have r₂ := b10e89 y
                 grind)
              | exact resolve b10e22 b10e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e89
            have b10e145 : False := by grind
            exact b10e145
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op y y) := by grind
            have b11e23 : y = (M.op y x) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            have b11e26 : x ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b11e17 X0 (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 X0 (σ y)
                 grind)
              | (have r₁ := b11e17 X0 (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b11e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e27
            have b11e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b11e28 (σ X0)
                 have i₂ := b11e20 X0 y
                 grind)
              | exact superpose b11e20 b11e28
              | exact resolve b11e28 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28
            have b11e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b11e15 (k X0 y)
                 have i₂ := b11e32 X0
                 grind)
              | exact superpose b11e32 b11e15
              | exact resolve b11e15 b11e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e36 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b11e35 X0
                 have i₂ := b11e15 X0
                 grind)
              | exact superpose b11e15 b11e35
              | exact resolve b11e35 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e35
            have b11e52 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by
              first
              | (have i₁ := b11e18 x y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x y
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e56 : y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
            clear b11e52
            have b11e58 : (M.op x y) = (k x y) := by
              first
              | (have r₁ := b11e56
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e56 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e56
            have b11e59 : x = (M.op x y) := by
              first
              | (have i₁ := b11e58
                 have i₂ := b11e36 x
                 grind)
              | exact superpose b11e36 b11e58
              | exact resolve b11e58 b11e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e36 b11e58
            have b11e60 : False := by grind
            exact b11e60
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : y ≠ (M.op y y) := by grind
            have b12e23 : y = (M.op y x) := by grind
            have b12e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b12e25 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e44 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by
              first
              | (have i₁ := b12e18 x y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e18
              | (have j0 := b12e18 x y
                 grind)
              | (have r₁ := b12e18 x y
                 have r₂ := b12e23
                 grind)
              | exact resolve b12e18 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e45 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b12e18 (σ x) (σ y)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e18
              | (have j0 := b12e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b12e18 (σ x) (σ y)
                 have r₂ := b12e25
                 grind)
              | exact resolve b12e18 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e49 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b12e45
            have b12e50 : y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
            clear b12e44
            have b12e52 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b12e49
                 have r₂ := b12e24
                 grind)
              | exact resolve b12e49 b12e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e49
            have b12e53 : (M.op x y) = (k x y) := by
              first
              | (have r₁ := b12e50
                 have r₂ := b12e22
                 grind)
              | exact resolve b12e50 b12e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e50
            have b12e54 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b12e52
                 have i₂ := b12e20 x y
                 grind)
              | exact superpose b12e20 b12e52
              | exact resolve b12e52 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e52
            have b12e55 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e54
                 have i₂ := b12e53
                 grind)
              | exact superpose b12e53 b12e54
              | exact resolve b12e54 b12e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e53 b12e54
            have b12e56 : False := by grind
            exact b12e56
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e23 : y ≠ (M.op y y) := by grind
              have b13e24 : y = (M.op y x) := by grind
              have b13e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b13e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b13e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e22
                | exact resolve b13e22 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e45 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b13e19 (σ x) (σ y)
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e19
                | (have j0 := b13e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b13e19 (σ x) (σ y)
                   have r₂ := b13e26
                   grind)
                | exact resolve b13e19 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e47 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by
                first
                | (have i₁ := b13e19 x y
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e19
                | (have j0 := b13e19 x y
                   grind)
                | (have r₁ := b13e19 x y
                   have r₂ := b13e24
                   grind)
                | exact resolve b13e19 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e48 : y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
              clear b13e47
              have b13e50 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
              clear b13e45
              have b13e52 : (M.op x y) = (k x y) := by
                first
                | (have r₁ := b13e48
                   have r₂ := b13e23
                   grind)
                | exact resolve b13e48 b13e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e48
              have b13e54 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b13e50
                   have r₂ := b13e25
                   grind)
                | exact resolve b13e50 b13e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e50
              have b13e56 : x = (k x y) := by
                first
                | (have i₁ := b13e52
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e52
                | exact resolve b13e52 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e52
              have b13e58 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b13e54
                   have i₂ := b13e21 x y
                   grind)
                | exact superpose b13e21 b13e54
                | exact resolve b13e54 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e54
              have b13e59 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e58
                   have i₂ := b13e56
                   grind)
                | exact superpose b13e56 b13e58
                | exact resolve b13e58 b13e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e56 b13e58
              have b13e60 : False := by grind
              exact b13e60
            · have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e23 : y ≠ (M.op y y) := by grind
              have b14e24 : y = (M.op y x) := by grind
              have b14e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b14e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e42 : y ≠ y ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by
                first
                | (have i₁ := b14e19 x y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e19
                | (have j0 := b14e19 x y
                   grind)
                | (have r₁ := b14e19 x y
                   have r₂ := b14e24
                   grind)
                | exact resolve b14e19 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e43 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b14e19 (σ x) (σ y)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e19
                | (have j0 := b14e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b14e19 (σ x) (σ y)
                   have r₂ := b14e26
                   grind)
                | exact resolve b14e19 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e47 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
              clear b14e43
              have b14e48 : y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
              clear b14e42
              have b14e50 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b14e47
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e47 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e47
              have b14e51 : (M.op x y) = (k x y) := by
                first
                | (have r₁ := b14e48
                   have r₂ := b14e23
                   grind)
                | exact resolve b14e48 b14e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e48
              have b14e52 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b14e50
                   have i₂ := b14e21 x y
                   grind)
                | exact superpose b14e21 b14e50
                | exact resolve b14e50 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e50
              have b14e53 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e52
                   have i₂ := b14e51
                   grind)
                | exact superpose b14e51 b14e52
                | exact resolve b14e52 b14e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e51 b14e52
              have b14e54 : False := by grind
              exact b14e54
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e17 X0 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e17
              | (have j0 := b15e17 X0 x
                 grind)
              | (have r₁ := b15e17 X0 x
                 have r₂ := b15e26
                 grind)
              | exact resolve b15e17 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e28 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27
            have b15e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                 have i₂ := b15e14 X0 (M.op X0 (M.op X2 X2)) X2
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 X1 (M.op X0 X0)
                 have i₂ := b15e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b15e32 X0 X1 x
                 have i₂ := b15e33 x X0
                 grind)
              | exact superpose b15e33 b15e32
              | exact resolve b15e32 b15e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e32
            have b15e35 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e33 x X0
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e33
              | exact resolve b15e33 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e33
            have b15e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 X0
                 have i₂ := b15e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e75 : ∀ X0 : G, x = (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b15e34 x X0
                 have i₂ := b15e35 X0
                 grind)
              | exact superpose b15e35 b15e34
              | exact resolve b15e34 b15e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e303 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e60 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e60
            have b15e305 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e303 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e303
            have b15e323 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = x := by
              intro X0
              first
              | (have i₁ := b15e305 X0
                 have i₂ := b15e75 (σ X0)
                 grind)
              | exact superpose b15e75 b15e305
              | (have j0 := b15e305 X0
                 grind)
              | exact resolve b15e305 b15e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e75 b15e305
            have b15e436 : (σ x) ≠ (σ x) ∨ x = (σ x) := by
              first
              | (have i₁ := b15e323 x
                 have i₂ := b15e28 x
                 grind)
              | exact superpose b15e28 b15e323
              | (have j0 := b15e323 x
                 grind)
              | exact resolve b15e323 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e323
            have b15e440 : x = (σ x) := by grind
            clear b15e436
            have b15e467 : (σ y) ≠ (M.op (σ y) x) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e440
                 grind)
              | exact superpose b15e440 b15e25
              | exact resolve b15e25 b15e440
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e440
            have b15e478 : False := by grind
            exact b15e478
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
                intro X0 X1 X2
                grind
              have b16e24 : y = (M.op y x) := by grind
              have b16e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e15 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                   have i₂ := b16e15 X0 (M.op X0 (M.op X2 X2)) X2
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X1 X1 (M.op X0 X0)
                   have i₂ := b16e15 (M.op X0 X0) X1 X0
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e34 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e32 X0 X1 x
                   have i₂ := b16e33 x X0
                   grind)
                | exact superpose b16e33 b16e32
                | exact resolve b16e32 b16e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e32
              have b16e73 : x = (M.op y y) := by
                first
                | (have i₁ := b16e34 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e34
                | exact resolve b16e34 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34
              have b16e84 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b16e33 y X0
                   have i₂ := b16e73
                   grind)
                | exact superpose b16e73 b16e33
                | exact resolve b16e33 b16e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e33 b16e73
              have b16e121 : x ≠ x := by
                first
                | (have i₁ := b16e27
                   have i₂ := b16e84 x
                   grind)
                | exact superpose b16e84 b16e27
                | (have r₁ := b16e27
                   have r₂ := b16e84 x
                   grind)
                | exact resolve b16e27 b16e84
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e84
              have b16e122 : False := by grind
              exact b16e122
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
                intro X0 X1 X2
                grind
              have b17e24 : y = (M.op y x) := by grind
              have b17e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e31 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                   have i₂ := b17e15 X0 (M.op X0 (M.op X2 X2)) X2
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X1 X1 (M.op X0 X0)
                   have i₂ := b17e15 (M.op X0 X0) X1 X0
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e33 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e31 X0 X1 x
                   have i₂ := b17e32 x X0
                   grind)
                | exact superpose b17e32 b17e31
                | exact resolve b17e31 b17e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e31
              have b17e49 : x = (M.op y y) := by
                first
                | (have i₁ := b17e33 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e33
                | exact resolve b17e33 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e33
              have b17e73 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b17e32 y X0
                   have i₂ := b17e49
                   grind)
                | exact superpose b17e49 b17e32
                | exact resolve b17e32 b17e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e32 b17e49
              have b17e91 : x ≠ x := by
                first
                | (have i₁ := b17e27
                   have i₂ := b17e73 x
                   grind)
                | exact superpose b17e73 b17e27
                | (have r₁ := b17e27
                   have r₂ := b17e73 x
                   grind)
                | exact resolve b17e27 b17e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e73
              have b17e92 : False := by grind
              exact b17e92
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b18e22 : y ≠ (M.op y x) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X1 X1 (M.op X0 X0)
               have i₂ := b18e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e38 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b18e36 x X0
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e36
            | exact resolve b18e36 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e56 : y ≠ y := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e38 y
               grind)
            | exact superpose b18e38 b18e22
            | (have r₁ := b18e22
               have r₂ := b18e38 y
               grind)
            | exact resolve b18e22 b18e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e38
          have b18e57 : False := by grind
          exact b18e57
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b19e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            have b19e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b19e21
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e21
              | exact resolve b19e21 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X1 X1 (M.op X0 X0)
                 have i₂ := b19e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e38 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b19e36 (σ y) X0
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e36
              | exact resolve b19e36 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e36
            have b19e58 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b19e27
                 have i₂ := b19e38 (σ x)
                 grind)
              | exact superpose b19e38 b19e27
              | (have r₁ := b19e27
                 have r₂ := b19e38 (σ x)
                 grind)
              | exact resolve b19e27 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e27 b19e38
            have b19e59 : False := by grind
            exact b19e59
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y y) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 X0 (σ y)
                 grind)
              | (have r₁ := b20e17 X0 (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b20e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e27
            have b20e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 X1 (τ X0)
                 have i₂ := b20e16 X0
                 grind)
              | exact superpose b20e16 b20e20
              | exact resolve b20e20 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b20e28 (σ X0)
                 have i₂ := b20e20 X0 y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e15 (k X0 y)
                 have i₂ := b20e32 X0
                 grind)
              | exact superpose b20e32 b20e15
              | exact resolve b20e15 b20e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e36 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e35 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e35
              | exact resolve b20e35 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b20e14 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                 have i₂ := b20e14 X0 (M.op X0 (M.op X2 X2)) X2
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e41 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b20e14 X1 X1 (M.op X0 X0)
                 have i₂ := b20e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e42 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b20e40 X0 X1 x
                 have i₂ := b20e41 x X0
                 grind)
              | exact superpose b20e41 b20e40
              | exact resolve b20e40 b20e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e40
            have b20e43 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e41 (σ y) X0
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e41
              | exact resolve b20e41 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e41
            have b20e67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e20 X1 X0
                 have i₂ := b20e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b20e19 b20e20
              | (have j1 := b20e19 (σ X0) (σ X0)
                 grind)
              | exact resolve b20e20 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e86 : ∀ X0 : G, (σ y) = (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b20e42 (σ y) X0
                 have i₂ := b20e43 X0
                 grind)
              | exact superpose b20e43 b20e42
              | exact resolve b20e42 b20e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e42 b20e43
            have b20e119 : y ≠ (σ y) := by
              first
              | (have i₁ := b20e22
                 have i₂ := b20e86 y
                 grind)
              | exact superpose b20e86 b20e22
              | exact resolve b20e22 b20e86
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e128 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b20e15 (k X0 (τ X1))
                 have i₂ := b20e30 X1 X0
                 grind)
              | exact superpose b20e30 b20e15
              | exact resolve b20e15 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e294 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b20e67 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e67
            have b20e296 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b20e294 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e294
            have b20e313 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ y) := by
              intro X0
              first
              | (have i₁ := b20e296 X0
                 have i₂ := b20e86 (σ X0)
                 grind)
              | exact superpose b20e86 b20e296
              | (have j0 := b20e296 X0
                 grind)
              | exact resolve b20e296 b20e86
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e86 b20e296
            have b20e388 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
              intro X0
              first
              | (have i₁ := b20e128 X0 y
                 have i₂ := b20e36 (σ X0)
                 grind)
              | exact superpose b20e36 b20e128
              | exact resolve b20e128 b20e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36 b20e128
            have b20e396 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e388 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e388
              | exact resolve b20e388 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e388
            have b20e427 : (σ (τ y)) ≠ (σ (τ y)) ∨ (σ y) = (σ (τ y)) := by
              first
              | (have i₁ := b20e313 (τ y)
                 have i₂ := b20e396 (τ y)
                 grind)
              | exact superpose b20e396 b20e313
              | (have j0 := b20e313 (τ y)
                 grind)
              | exact resolve b20e313 b20e396
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e313 b20e396
            have b20e430 : (σ y) = (σ (τ y)) := by grind
            clear b20e427
            have b20e438 : y = (σ y) := by
              first
              | (have i₁ := b20e430
                 have i₂ := b20e16 y
                 grind)
              | exact superpose b20e16 b20e430
              | exact resolve b20e430 b20e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e430
            have b20e444 : False := by grind
            exact b20e444
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b21e23 : y ≠ (M.op y x) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 X1 (M.op X0 X0)
                 have i₂ := b21e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e35 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b21e33 x X0
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e33
              | exact resolve b21e33 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e33
            have b21e56 : y ≠ y := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e35 y
                 grind)
              | exact superpose b21e35 b21e23
              | (have r₁ := b21e23
                 have r₂ := b21e35 y
                 grind)
              | exact resolve b21e23 b21e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e35
            have b21e57 : False := by grind
            exact b21e57
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
                intro X0 X1 X2
                grind
              have b22e23 : y ≠ (M.op y y) := by grind
              have b22e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e15 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                   have i₂ := b22e15 X0 (M.op X0 (M.op X2 X2)) X2
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X1 X1 (M.op X0 X0)
                   have i₂ := b22e15 (M.op X0 X0) X1 X0
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e34 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b22e32 X0 X1 x
                   have i₂ := b22e33 x X0
                   grind)
                | exact superpose b22e33 b22e32
                | exact resolve b22e32 b22e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e32
              have b22e54 : y = (M.op x x) := by
                first
                | (have i₁ := b22e34 y x
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e34
                | exact resolve b22e34 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e34
              have b22e79 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b22e33 x X0
                   have i₂ := b22e54
                   grind)
                | exact superpose b22e54 b22e33
                | exact resolve b22e33 b22e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e33 b22e54
              have b22e97 : y ≠ y := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e79 y
                   grind)
                | exact superpose b22e79 b22e23
                | (have r₁ := b22e23
                   have r₂ := b22e79 y
                   grind)
                | exact resolve b22e23 b22e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e79
              have b22e98 : False := by grind
              exact b22e98
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b23e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 (τ X0)
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e21
                | exact resolve b23e21 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e31 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                   have i₂ := b23e15 X0 (M.op X0 (M.op X2 X2)) X2
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X1 X1 (M.op X0 X0)
                   have i₂ := b23e15 (M.op X0 X0) X1 X0
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e33 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b23e31 X0 X1 x
                   have i₂ := b23e32 x X0
                   grind)
                | exact superpose b23e32 b23e31
                | exact resolve b23e31 b23e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e31
              have b23e37 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 (M.op X0 X0) X1 X0
                   have i₂ := b23e32 (M.op X0 X0) X1
                   grind)
                | exact superpose b23e32 b23e15
                | exact resolve b23e15 b23e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e18 X1 (M.op X0 X0)
                   have i₂ := b23e32 X0 (M.op X0 X0)
                   grind)
                | exact superpose b23e32 b23e18
                | (have j0 := b23e18 X1 (M.op X0 X0)
                   grind)
                | (have r₁ := b23e18 X0 (M.op X0 X0)
                   have r₂ := b23e32 X0 (M.op X0 X0)
                   grind)
                | exact resolve b23e18 b23e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e32
              have b23e41 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have j0 := b23e40 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e40
              have b23e50 : (σ x) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e33 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e33
                | exact resolve b23e33 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e33
              have b23e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 X0
                   have i₂ := b23e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b23e20 b23e21
                | (have j1 := b23e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b23e21 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e103 : ∀ X0 : G, x ≠ (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b23e27
                   have i₂ := b23e37 X0 x
                   grind)
                | (have i₁ := b23e27
                   have i₂ := b23e37 x X0
                   grind)
                | exact superpose b23e37 b23e27
                | exact resolve b23e27 b23e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e124 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e16 (k X0 (τ X1))
                   have i₂ := b23e30 X1 X0
                   grind)
                | exact superpose b23e30 b23e16
                | exact resolve b23e16 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30
              have b23e178 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b23e37 (σ y) X0
                   have i₂ := b23e50
                   grind)
                | exact superpose b23e50 b23e37
                | exact resolve b23e37 b23e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37
              have b23e181 : x ≠ (σ x) := by
                first
                | (have i₁ := b23e103 (σ y)
                   have i₂ := b23e50
                   grind)
                | exact superpose b23e50 b23e103
                | exact resolve b23e103 b23e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e50 b23e103
              have b23e230 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b23e59 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e59
              have b23e232 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b23e230 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e230
              have b23e253 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ x) := by
                intro X0
                first
                | (have i₁ := b23e232 X0
                   have i₂ := b23e178 (σ X0)
                   grind)
                | exact superpose b23e178 b23e232
                | (have j0 := b23e232 X0
                   grind)
                | exact resolve b23e232 b23e178
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e232
              have b23e378 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b23e124 X0 (M.op X1 X1)
                   have i₂ := b23e41 X1 (σ X0)
                   grind)
                | exact superpose b23e41 b23e124
                | exact resolve b23e124 b23e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e41
              have b23e386 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
                intro X0
                first
                | (have i₁ := b23e378 X0 x
                   have i₂ := b23e178 x
                   grind)
                | exact superpose b23e178 b23e378
                | exact resolve b23e378 b23e178
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e178 b23e378
              have b23e391 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b23e386 X0
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e386
                | exact resolve b23e386 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e386
              have b23e392 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e391 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e391
                | exact resolve b23e391 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e391
              have b23e397 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ x)) := by
                intro X0
                first
                | (have i₁ := b23e124 X0 x
                   have i₂ := b23e392 (σ X0)
                   grind)
                | exact superpose b23e392 b23e124
                | exact resolve b23e124 b23e392
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e124 b23e392
              have b23e400 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e397 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e397
                | exact resolve b23e397 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e397
              have b23e504 : (σ (τ x)) ≠ (σ (τ x)) ∨ (σ x) = (σ (τ x)) := by
                first
                | (have i₁ := b23e253 (τ x)
                   have i₂ := b23e400 (τ x)
                   grind)
                | exact superpose b23e400 b23e253
                | (have j0 := b23e253 (τ x)
                   grind)
                | exact resolve b23e253 b23e400
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e253 b23e400
              have b23e509 : (σ x) = (σ (τ x)) := by grind
              clear b23e504
              have b23e513 : x = (σ x) := by
                first
                | (have i₁ := b23e509
                   have i₂ := b23e17 x
                   grind)
                | exact superpose b23e17 b23e509
                | exact resolve b23e509 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e509
              have b23e517 : False := by grind
              exact b23e517
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e23 : y ≠ (M.op y x) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 X1 (M.op X0 X0)
                 have i₂ := b24e14 (M.op X0 X0) X1 X0
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e35 : ∀ X0 : G, (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b24e33 x X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e33
              | exact resolve b24e33 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33
            have b24e52 : y ≠ y := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e35 y
                 grind)
              | exact superpose b24e35 b24e23
              | (have r₁ := b24e23
                 have r₂ := b24e35 y
                 grind)
              | exact resolve b24e23 b24e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e35
            have b24e53 : False := by grind
            exact b24e53
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
                intro X0 X1 X2
                grind
              have b25e23 : y ≠ (M.op y y) := by grind
              have b25e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                   have i₂ := b25e15 X0 (M.op X0 (M.op X2 X2)) X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 X1 (M.op X0 X0)
                   have i₂ := b25e15 (M.op X0 X0) X1 X0
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e34 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e32 X0 X1 x
                   have i₂ := b25e33 x X0
                   grind)
                | exact superpose b25e33 b25e32
                | exact resolve b25e32 b25e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e32
              have b25e50 : y = (M.op x x) := by
                first
                | (have i₁ := b25e34 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e34
                | exact resolve b25e34 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34
              have b25e74 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b25e33 x X0
                   have i₂ := b25e50
                   grind)
                | exact superpose b25e50 b25e33
                | exact resolve b25e33 b25e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e33 b25e50
              have b25e92 : y ≠ y := by
                first
                | (have i₁ := b25e23
                   have i₂ := b25e74 y
                   grind)
                | exact superpose b25e74 b25e23
                | (have r₁ := b25e23
                   have r₂ := b25e74 y
                   grind)
                | exact resolve b25e23 b25e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e74
              have b25e93 : False := by grind
              exact b25e93
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e27 : x ≠ (M.op x x) := by grind
              have b26e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 (τ X0) X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
              have b26e31 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
                   have i₂ := b26e15 X0 (M.op X0 (M.op X2 X2)) X2
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X1 X1 (M.op X0 X0)
                   have i₂ := b26e15 (M.op X0 X0) X1 X0
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e33 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e31 X0 X1 x
                   have i₂ := b26e32 x X0
                   grind)
                | exact superpose b26e32 b26e31
                | exact resolve b26e31 b26e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e31
              have b26e37 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 (M.op X0 X0) X1 X0
                   have i₂ := b26e32 (M.op X0 X0) X1
                   grind)
                | exact superpose b26e32 b26e15
                | exact resolve b26e15 b26e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X1 (M.op X0 X0)
                   have i₂ := b26e32 X0 (M.op X0 X0)
                   grind)
                | exact superpose b26e32 b26e18
                | (have j0 := b26e18 X1 (M.op X0 X0)
                   grind)
                | (have r₁ := b26e18 X0 (M.op X0 X0)
                   have r₂ := b26e32 X0 (M.op X0 X0)
                   grind)
                | exact resolve b26e18 b26e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e32
              have b26e41 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e40 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e40
              have b26e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X0) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 X1 X0
                   have i₂ := b26e20 X2 X0
                   grind)
                | exact superpose b26e20 b26e18
                | (have j0 := b26e18 X1 X0
                   have j1 := b26e20 X2 X0
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X0
                   have r₂ := b26e20 X0 X0
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e61 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (σ y)
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ y) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e62 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have j0 := b26e61 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e61
              have b26e63 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = X0 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e57 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e57
              have b26e91 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 X2 X1
                   have i₂ := b26e37 X0 X1
                   grind)
                | (have i₁ := b26e18 X2 X1
                   have i₂ := b26e37 X1 X0
                   grind)
                | exact superpose b26e37 b26e18
                | (have j0 := b26e18 X2 X1
                   grind)
                | (have r₁ := b26e18 X0 (M.op X0 X0)
                   have r₂ := b26e37 X0 (M.op X0 X0)
                   grind)
                | (have r₁ := b26e18 X0 (M.op X1 X1)
                   have r₂ := b26e37 (M.op X1 X1) X1
                   grind)
                | exact resolve b26e18 b26e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e97 : ∀ X0 : G, (σ y) ≠ (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e37 X0 (σ y)
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e37 (σ y) X0
                   grind)
                | exact superpose b26e37 b26e25
                | exact resolve b26e25 b26e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e98 : ∀ X0 : G, x ≠ (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b26e27
                   have i₂ := b26e37 X0 x
                   grind)
                | (have i₁ := b26e27
                   have i₂ := b26e37 x X0
                   grind)
                | exact superpose b26e37 b26e27
                | exact resolve b26e27 b26e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e105 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e29 X1 X0
                   have i₂ := b26e20 (τ X1) X0
                   grind)
                | exact superpose b26e20 b26e29
                | (have j1 := b26e20 X0 X0
                   grind)
                | exact resolve b26e29 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e119 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k X0 (τ X1))
                   have i₂ := b26e30 X1 X0
                   grind)
                | exact superpose b26e30 b26e16
                | exact resolve b26e16 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30
              have b26e127 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 y
                   have i₂ := b26e62 (σ X0)
                   grind)
                | exact superpose b26e62 b26e21
                | (have j1 := b26e62 (σ X0)
                   grind)
                | exact resolve b26e21 b26e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e62
              have b26e139 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e63 (σ X0) X2 (σ X1)
                   grind)
                | exact superpose b26e63 b26e21
                | (have j1 := b26e63 (σ X0) X2 (σ X1)
                   grind)
                | exact resolve b26e21 b26e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e141 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 ∨ (M.op X0 (τ X1)) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e29 X1 X0
                   have i₂ := b26e63 X0 X2 (τ X1)
                   grind)
                | exact superpose b26e63 b26e29
                | (have j1 := b26e63 X0 X2 (τ X1)
                   grind)
                | exact resolve b26e29 b26e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e63
              have b26e179 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) ∨ (σ X1) = (M.op X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e54 X0 X0
                   have i₂ := b26e37 X0 (σ X0)
                   grind)
                | (have i₁ := b26e54 X0 X0
                   have i₂ := b26e37 (σ X0) X1
                   grind)
                | exact superpose b26e37 b26e54
                | exact resolve b26e54 b26e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e54
              have b26e232 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e179 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e179
              have b26e279 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e119 X0 (M.op X1 X1)
                   have i₂ := b26e41 X1 (σ X0)
                   grind)
                | exact superpose b26e41 b26e119
                | exact resolve b26e119 b26e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e41
              have b26e287 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e279 X0 X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e279
                | exact resolve b26e279 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e279
              have b26e324 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e119 X0 (τ (M.op X1 X1))
                   have i₂ := b26e287 (σ X0) X1
                   grind)
                | exact superpose b26e287 b26e119
                | exact resolve b26e119 b26e287
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e287
              have b26e334 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e324 X0 X1
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e324
                | exact resolve b26e324 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e324
              have b26e1039 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ (k y y))))) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X1 X0 (σ y)
                   have i₂ := b26e127 y
                   grind)
                | exact superpose b26e127 b26e15
                | (have j1 := b26e127 y
                   grind)
                | exact resolve b26e15 b26e127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e1055 : ∀ X0 : G, (k X0 (τ (τ (σ (k y y))))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e334 X0 (σ y)
                   have i₂ := b26e127 y
                   grind)
                | exact superpose b26e127 b26e334
                | (have j1 := b26e127 y
                   grind)
                | exact resolve b26e334 b26e127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e127 b26e334
              have b26e1067 : ∀ X0 : G, (k X0 (τ (τ (σ (k y y))))) = X0 := by
                intro X0
                first
                | (have j0 := b26e1055 X0
                   grind)
                | (have r₁ := b26e1055 X0
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1055 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1055
              have b26e1070 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ (k y y))))) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e1039 X0 X1
                   grind)
                | (have r₁ := b26e1039 X0 X1
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1039 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1039
              have b26e1076 : ∀ X0 : G, (k X0 (τ (k y y))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e1067 X0
                   have i₂ := b26e16 (k y y)
                   grind)
                | exact superpose b26e16 b26e1067
                | exact resolve b26e1067 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1067
              have b26e1078 : ∀ X1 : G, (M.op X1 (σ (k y y))) = X1 := by
                intro X1
                first
                | (have i₁ := b26e1070 x X1
                   have i₂ := b26e33 (M.op X1 (σ (k y y))) x
                   grind)
                | exact superpose b26e33 b26e1070
                | exact resolve b26e1070 b26e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1070
              have b26e1242 : ∀ X0 : G, (M.op X0 X0) = (σ (k y y)) := by
                intro X0
                first
                | (have i₁ := b26e33 (σ (k y y)) X0
                   have i₂ := b26e1078 X0
                   grind)
                | exact superpose b26e1078 b26e33
                | exact resolve b26e33 b26e1078
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1078
              have b26e1297 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e105 X0 (σ X0)
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e105
                | (have j0 := b26e105 X1 X1
                   grind)
                | exact resolve b26e105 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e105
              have b26e1375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e1297 X0 X1
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e1297
                | (have j0 := b26e1297 X1 X1
                   grind)
                | exact resolve b26e1297 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1297
              have b26e1394 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) ∨ (k X2 (τ X1)) = X2 ∨ (M.op X0 X0) = (τ X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e141 (τ X1) X1 X2
                   have i₂ := b26e37 X0 (τ X1)
                   grind)
                | (have i₁ := b26e141 (τ X1) X1 X2
                   have i₂ := b26e37 (τ X1) X1
                   grind)
                | exact superpose b26e37 b26e141
                | (have j0 := b26e141 (τ X1) X1 X2
                   grind)
                | exact resolve b26e141 b26e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e37 b26e141
              have b26e1480 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) ∨ (k X2 (τ X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e1394 X0 X1 X2
                   have j1 := b26e91 X0 (τ X1) X2
                   grind)
                | (have r₁ := b26e1394 X0 X1 (M.op X0 X0)
                   have r₂ := b26e91 X0 (k (M.op X0 X0) (τ X1)) X2
                   grind)
                | (have r₁ := b26e1394 X0 X1 X2
                   have r₂ := b26e91 X0 (τ X1) X2
                   grind)
                | exact resolve b26e1394 b26e91
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e91 b26e1394
              have b26e1489 : ∀ X0 X1 X2 : G, (k X1 X1) = (σ (M.op X0 X0)) ∨ (k X2 (τ X1)) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e1480 X0 X1 X2
                   have i₂ := b26e17 X1
                   grind)
                | exact superpose b26e17 b26e1480
                | (have j0 := b26e1480 X0 X1 X2
                   grind)
                | exact resolve b26e1480 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1480
              have b26e2028 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e22
                   have i₂ := b26e139 x y X0
                   grind)
                | exact superpose b26e139 b26e22
                | (have j1 := b26e139 x y X0
                   grind)
                | exact resolve b26e22 b26e139
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e139
              have b26e4088 : ∀ X0 : G, (k y y) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e16 (k y y)
                   have i₂ := b26e1242 X0
                   grind)
                | exact superpose b26e1242 b26e16
                | exact resolve b26e16 b26e1242
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1242
              have b26e4282 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e29 X1 (τ X1)
                   have i₂ := b26e232 X0 (τ X1)
                   grind)
                | exact superpose b26e232 b26e29
                | (have j1 := b26e232 X0 (τ X1)
                   grind)
                | exact resolve b26e29 b26e232
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29
              have b26e4359 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e4282 X0 X1
                   have i₂ := b26e17 X1
                   grind)
                | exact superpose b26e17 b26e4282
                | (have j0 := b26e4282 X0 X1
                   grind)
                | exact resolve b26e4282 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4282
              have b26e4409 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e4359 X0 X1
                   have i₂ := b26e17 X1
                   grind)
                | exact superpose b26e17 b26e4359
                | (have j0 := b26e4359 X0 X1
                   grind)
                | exact resolve b26e4359 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4359
              have b26e5189 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k y y))) ∨ (M.op X0 X0) = (σ (τ (k y y))) := by
                intro X0
                first
                | (have i₁ := b26e232 X0 (τ (k y y))
                   have i₂ := b26e1076 (τ (k y y))
                   grind)
                | exact superpose b26e1076 b26e232
                | (have j0 := b26e232 X0 (τ (k y y))
                   grind)
                | exact resolve b26e232 b26e1076
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e232 b26e1076
              have b26e5215 : ∀ X0 : G, (M.op X0 X0) = (σ (τ (k y y))) := by
                intro X0
                first
                | (have j0 := b26e5189 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5189
              have b26e5231 : ∀ X0 : G, (M.op X0 X0) = (k y y) := by
                intro X0
                first
                | (have i₁ := b26e5215 X0
                   have i₂ := b26e17 (k y y)
                   grind)
                | exact superpose b26e17 b26e5215
                | exact resolve b26e5215 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5215
              have b26e5399 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X0))) = (k X1 (τ (σ X1))) ∨ (k X2 (τ (σ X1))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e119 X1 (σ X1)
                   have i₂ := b26e1489 X0 (σ X1) X2
                   grind)
                | exact superpose b26e1489 b26e119
                | (have j1 := b26e1489 X0 (σ X1) X2
                   grind)
                | exact resolve b26e119 b26e1489
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e119 b26e1489
              have b26e5538 : ∀ X0 X1 X2 : G, (k X1 X1) = (τ (σ (M.op X0 X0))) ∨ (k X2 (τ (σ X1))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e5399 X0 X1 X2
                   have i₂ := b26e16 X1
                   grind)
                | exact superpose b26e16 b26e5399
                | (have j0 := b26e5399 X0 X1 X2
                   grind)
                | exact resolve b26e5399 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5399
              have b26e5600 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X2 (τ (σ X1))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e5538 X0 X1 X2
                   have i₂ := b26e16 (M.op X0 X0)
                   grind)
                | exact superpose b26e16 b26e5538
                | (have j0 := b26e5538 X0 X1 X2
                   grind)
                | exact resolve b26e5538 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5538
              have b26e5626 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (M.op X0 X0) = (k X1 X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e5600 X0 X1 X2
                   have i₂ := b26e16 X1
                   grind)
                | exact superpose b26e16 b26e5600
                | (have j0 := b26e5600 X0 X1 X2
                   grind)
                | exact resolve b26e5600 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5600
              have b26e5722 : ∀ X0 : G, (M.op X0 (k y y)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e33 X0 X0
                   have i₂ := b26e5231 X0
                   grind)
                | exact superpose b26e5231 b26e33
                | exact resolve b26e33 b26e5231
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5231
              have b26e7475 : (k y y) = (τ (k y y)) := by
                first
                | (have i₁ := b26e4088 (k y y)
                   have i₂ := b26e5722 (k y y)
                   grind)
                | exact superpose b26e5722 b26e4088
                | exact resolve b26e4088 b26e5722
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4088 b26e5722
              have b26e49012 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e5626 X1 X0 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5626
              have b26e49035 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
                intro X0 X1
                first
                | (have j0 := b26e49012 X0 X1
                   have j1 := b26e4409 X1 X0
                   grind)
                | (have r₁ := b26e49012 (k X1 X1) X0
                   have r₂ := b26e4409 X0 X1
                   grind)
                | (have r₁ := b26e49012 X1 X0
                   have r₂ := b26e4409 X0 X1
                   grind)
                | (have r₁ := b26e49012 (M.op X0 X0) X1
                   have r₂ := b26e4409 X0 (M.op X1 X1)
                   grind)
                | exact resolve b26e49012 b26e4409
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4409 b26e49012
              have b26e49877 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
                intro X0 X2
                first
                | (have i₁ := b26e49035 X2 x
                   have i₂ := b26e49035 X0 x
                   grind)
                | exact superpose b26e49035 b26e49035
                | exact resolve b26e49035 b26e49035
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e49992 : ∀ X0 : G, x ≠ (k X0 X0) := by
                intro X0
                first
                | (have i₁ := b26e98 x
                   have i₂ := b26e49035 X0 x
                   grind)
                | exact superpose b26e49035 b26e98
                | exact resolve b26e98 b26e49035
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e98 b26e49035
              have b26e53796 : ∀ X0 : G, (k X0 X0) = (τ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e7475
                   have i₂ := b26e49877 y x
                   grind)
                | (have i₁ := b26e7475
                   have i₂ := b26e49877 X0 y
                   grind)
                | exact superpose b26e49877 b26e7475
                | exact resolve b26e7475 b26e49877
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e7475 b26e49877
              have b26e59998 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b26e2028 X0
                   have i₂ := b26e1375 y x
                   grind)
                | exact superpose b26e1375 b26e2028
                | (have j0 := b26e2028 X0
                   have j1 := b26e1375 x x
                   grind)
                | (have r₁ := b26e2028 X0
                   have r₂ := b26e1375 y x
                   grind)
                | exact resolve b26e2028 b26e1375
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1375 b26e2028
              have b26e60000 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e59998 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e59998
              have b26e60006 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have j0 := b26e60000 X0
                   grind)
                | (have r₁ := b26e60000 X0
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e60000 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60000
              have b26e60012 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have j0 := b26e60006 X0
                   grind)
                | (have r₁ := b26e60006 X0
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e60006 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60006
              have b26e493889 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e33 (σ y) (σ x)
                   have i₂ := b26e60012 X0
                   grind)
                | exact superpose b26e60012 b26e33
                | (have j1 := b26e60012 X0
                   grind)
                | exact resolve b26e33 b26e60012
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33 b26e60012
              have b26e493907 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b26e493889 X0
                   grind)
                | (have r₁ := b26e493889 X0
                   have r₂ := b26e97 (σ x)
                   grind)
                | exact resolve b26e493889 b26e97
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e97 b26e493889
              have b26e496166 : x ≠ (σ x) := by
                first
                | (have i₁ := b26e49992 (σ x)
                   have i₂ := b26e493907 (σ x)
                   grind)
                | exact superpose b26e493907 b26e49992
                | exact resolve b26e49992 b26e493907
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49992
              have b26e496195 : (σ x) = (τ (σ x)) := by
                first
                | (have i₁ := b26e53796 (σ x)
                   have i₂ := b26e493907 (σ x)
                   grind)
                | exact superpose b26e493907 b26e53796
                | exact resolve b26e53796 b26e493907
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e53796 b26e493907
              have b26e496468 : x = (σ x) := by
                first
                | (have i₁ := b26e496195
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e496195
                | exact resolve b26e496195 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e496195
              have b26e496652 : False := by grind
              exact b26e496652

/-- `Equation647`: `x = x ◇ (y ◇ ((y ◇ z) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation647 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law647 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law647.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e22 : x = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e25 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b0e15 y x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have j0 := b0e15 y x
             grind)
          | (have r₁ := b0e15 y x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e28 : y = (k y x) := by grind
        clear b0e25
        have b0e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 X1 X0
             have i₂ := b0e17 (σ X1) (σ X0)
             grind)
          | exact superpose b0e17 b0e18
          | (have j1 := b0e17 (σ X1) (σ X0)
             grind)
          | exact resolve b0e18 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e128 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b0e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e56
        have b0e721 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e128 x y
             have i₂ := b0e28
             grind)
          | exact superpose b0e28 b0e128
          | (have j0 := b0e128 x y
             grind)
          | exact resolve b0e128 b0e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e128
        have b0e724 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b0e721
        have b0e736 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b0e724
             have r₂ := b0e23
             grind)
          | exact resolve b0e724 b0e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e724
        have b0e752 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b0e23
             have i₂ := b0e736
             grind)
          | exact superpose b0e736 b0e23
          | exact resolve b0e23 b0e736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23
        have b0e755 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b0e16 (σ y) (σ x)
             have i₂ := b0e736
             grind)
          | exact superpose b0e736 b0e16
          | (have j0 := b0e16 (σ y) (σ x)
             grind)
          | (have r₁ := b0e16 (σ y) (σ x)
             have r₂ := b0e736
             grind)
          | exact resolve b0e16 b0e736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e736
        have b0e758 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b0e755
        have b0e761 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b0e758
             have i₂ := b0e18 y x
             grind)
          | exact superpose b0e18 b0e758
          | exact resolve b0e758 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e758
        have b0e764 : (σ x) = (σ (k y x)) := by
          first
          | (have r₁ := b0e761
             have r₂ := b0e752
             grind)
          | exact resolve b0e761 b0e752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e761
        have b0e765 : (σ x) = (σ y) := by
          first
          | (have i₁ := b0e764
             have i₂ := b0e28
             grind)
          | exact superpose b0e28 b0e764
          | exact resolve b0e764 b0e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e28 b0e764
        have b0e766 : False := by grind
        exact b0e766
      · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
        · have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b1e23 : x ≠ (M.op x y) := by grind
          have b1e24 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : x ≠ y := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e23
            | exact resolve b1e23 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e26 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e20
            | exact resolve b1e20 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e58 : y ≠ y ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b1e17 y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e17
            | (have j0 := b1e17 y x
               grind)
            | (have r₁ := b1e17 y x
               have r₂ := b1e24
               grind)
            | exact resolve b1e17 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e59 : x = y ∨ x = (k y x) := by grind
          clear b1e58
          have b1e60 : x = (k y x) := by
            first
            | (have r₁ := b1e59
               have r₂ := b1e25
               grind)
            | exact resolve b1e59 b1e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e25 b1e59
          have b1e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 X0
               have i₂ := b1e18 (σ X1) (σ X0)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X0)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e141 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e16 (σ X0) (σ X1)
               have i₂ := b1e64 X1 X0
               grind)
            | exact superpose b1e64 b1e16
            | (have j0 := b1e16 (σ X0) (σ X1)
               have j1 := b1e64 X1 X0
               grind)
            | (have r₁ := b1e16 (σ X1) (σ X1)
               have r₂ := b1e64 X1 X1
               grind)
            | (have r₁ := b1e16 (σ X1) (σ X0)
               have r₂ := b1e64 X0 X1
               grind)
            | exact resolve b1e16 b1e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e64
          have b1e145 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b1e141 X0 X1
               have j1 := b1e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b1e141 X0 X0
               have r₂ := b1e16 (σ X0) (σ X0)
               grind)
            | (have r₁ := b1e141 X0 X1
               have r₂ := b1e16 (σ X0) (σ X1)
               grind)
            | exact resolve b1e141 b1e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e141
          have b1e149 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e145 X0 X1
               have i₂ := b1e19 X0 X1
               grind)
            | exact superpose b1e19 b1e145
            | (have j0 := b1e145 X0 X1
               grind)
            | exact resolve b1e145 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e145
          have b1e608 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e149 y x
               have i₂ := b1e60
               grind)
            | exact superpose b1e60 b1e149
            | (have j0 := b1e149 y x
               grind)
            | exact resolve b1e149 b1e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e60 b1e149
          have b1e611 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b1e608
          have b1e614 : (σ x) = (σ y) := by
            first
            | (have r₁ := b1e611
               have r₂ := b1e26
               grind)
            | exact resolve b1e611 b1e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e611
          have b1e626 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e614
               grind)
            | exact superpose b1e614 b1e26
            | exact resolve b1e26 b1e614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26
          have b1e627 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e22
               have i₂ := b1e614
               grind)
            | exact superpose b1e614 b1e22
            | exact resolve b1e22 b1e614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e614
          have b1e657 : False := by grind
          exact b1e657
        · have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e23 : x ≠ (M.op x y) := by grind
          have b2e24 : y ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b2e112 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e60 x y
               grind)
            | exact superpose b2e60 b2e20
            | (have j1 := b2e60 x y
               grind)
            | exact resolve b2e20 b2e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e60
          have b2e816 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b2e112
               have i₂ := b2e18 y x
               grind)
            | exact superpose b2e18 b2e112
            | (have j1 := b2e18 (σ y) (σ x)
               grind)
            | exact resolve b2e112 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e112
          have b2e817 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b2e816
          have b2e818 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b2e817
               have r₂ := b2e24
               grind)
            | exact resolve b2e817 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e817
          have b2e819 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b2e818
               have r₂ := b2e23
               grind)
            | exact resolve b2e818 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e818
          have b2e1597 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e16 (σ y) (σ x)
               have i₂ := b2e819
               grind)
            | exact superpose b2e819 b2e16
            | (have j0 := b2e16 (σ y) (σ x)
               grind)
            | (have r₁ := b2e16 (σ y) (σ x)
               have r₂ := b2e819
               grind)
            | exact resolve b2e16 b2e819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e819
          have b2e1599 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b2e1597
          have b2e1600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e1599
               have i₂ := b2e19 y x
               grind)
            | exact superpose b2e19 b2e1599
            | exact resolve b2e1599 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1599
          have b2e1914 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e17 (σ y) (σ x)
               have i₂ := b2e1600
               grind)
            | exact superpose b2e1600 b2e17
            | (have j0 := b2e17 (σ y) (σ x)
               grind)
            | (have r₁ := b2e17 (σ y) (σ x)
               have r₂ := b2e1600
               grind)
            | exact resolve b2e17 b2e1600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e1916 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e16 (σ y) (σ x)
               have i₂ := b2e1600
               grind)
            | exact superpose b2e1600 b2e16
            | (have j0 := b2e16 (σ y) (σ x)
               grind)
            | exact resolve b2e16 b2e1600
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1600
          have b2e1917 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by grind
          clear b2e1914
          have b2e1919 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e1916
               have i₂ := b2e19 y x
               grind)
            | exact superpose b2e19 b2e1916
            | exact resolve b2e1916 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1916
          have b2e1920 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) := by grind
          clear b2e1919
          have b2e1922 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e1917
               have i₂ := b2e19 y x
               grind)
            | exact superpose b2e19 b2e1917
            | exact resolve b2e1917 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1917
          have b2e1926 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b2e1922
               have r₂ := b2e1920
               grind)
            | exact resolve b2e1922 b2e1920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1920 b2e1922
          have b2e17577 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e14 (k y x)
               have i₂ := b2e1926
               grind)
            | exact superpose b2e1926 b2e14
            | exact resolve b2e14 b2e1926
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1926
          have b2e17640 : (σ y) = (σ (k y x)) ∨ x = (k y x) := by
            first
            | (have i₁ := b2e17577
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e17577
            | exact resolve b2e17577 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e17577
          have b2e17845 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b2e17640
               have i₂ := b2e18 y x
               grind)
            | exact superpose b2e18 b2e17640
            | (have j1 := b2e18 y x
               grind)
            | exact resolve b2e17640 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e17640
          have b2e17900 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b2e17845
          have b2e17920 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b2e17900
               have r₂ := b2e23
               grind)
            | exact resolve b2e17900 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e17900
          have b2e17923 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b2e17920
               have r₂ := b2e24
               grind)
            | exact resolve b2e17920 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e17920
          have b2e18100 : (M.op x y) = (τ (σ y)) := by
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e17923
               grind)
            | exact superpose b2e17923 b2e14
            | exact resolve b2e14 b2e17923
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e17923
          have b2e18160 : y = (M.op x y) := by
            first
            | (have i₁ := b2e18100
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e18100
            | exact resolve b2e18100 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e18100
          have b2e18161 : False := by grind
          exact b2e18161
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : y = (M.op y x) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e27 : y ≠ y ∨ x = (k x y) := by
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
          have b3e31 : x = (k x y) := by grind
          clear b3e27
          have b3e53 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ y)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e54 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b3e53
          have b3e55 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e54
               have r₂ := b3e25
               grind)
            | exact resolve b3e54 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e54
          have b3e56 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b3e55
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e55
            | exact resolve b3e55 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e55
          have b3e57 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e56
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e56
            | exact resolve b3e56 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e56
          have b3e58 : False := by grind
          exact b3e58
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : y = (M.op y x) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e23
              | exact resolve b4e23 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e30 : y ≠ y ∨ x = (k x y) := by
              first
              | (have i₁ := b4e17 x y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e17
              | (have j0 := b4e17 x y
                 grind)
              | (have r₁ := b4e17 x y
                 have r₂ := b4e22
                 grind)
              | exact resolve b4e17 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e33 : x = (k x y) := by grind
            clear b4e30
            have b4e54 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e18 (σ x) (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e57 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b4e54
            have b4e59 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e57
                 have r₂ := b4e28
                 grind)
              | exact resolve b4e57 b4e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e57
            have b4e60 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b4e59
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e59
              | exact resolve b4e59 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e59
            have b4e61 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e60
                 have i₂ := b4e33
                 grind)
              | exact superpose b4e33 b4e60
              | exact resolve b4e60 b4e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33 b4e60
            have b4e62 : False := by grind
            exact b4e62
          · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op y x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e23
              | exact resolve b5e23 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e28 : y ≠ y ∨ x = (k x y) := by
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
            have b5e30 : x = (k x y) := by grind
            clear b5e28
            have b5e50 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b5e18 (σ x) (σ y)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e18
              | (have j0 := b5e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b5e18 (σ x) (σ y)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e18 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e51 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b5e50
            have b5e52 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e51
                 have r₂ := b5e27
                 grind)
              | exact resolve b5e51 b5e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e51
            have b5e53 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b5e52
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e52
              | exact resolve b5e52 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e52
            have b5e54 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e53
                 have i₂ := b5e30
                 grind)
              | exact superpose b5e30 b5e53
              | exact resolve b5e53 b5e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e53
            have b5e55 : False := by grind
            exact b5e55
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : y ≠ y ∨ x = (k x y) := by
            first
            | (have i₁ := b6e16 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 x y
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e29 : x = (k x y) := by grind
          clear b6e26
          have b6e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 X0
               have i₂ := b6e18 (σ X1) (σ X0)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X1) (σ X0)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e137 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b6e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e57
          have b6e690 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b6e137 y x
               have i₂ := b6e29
               grind)
            | exact superpose b6e29 b6e137
            | (have j0 := b6e137 y x
               grind)
            | exact resolve b6e137 b6e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e29 b6e137
          have b6e695 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b6e690
          have b6e707 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b6e695
               have r₂ := b6e23
               grind)
            | exact resolve b6e695 b6e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e695
          have b6e713 : False := by grind
          exact b6e713
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X1 (τ X0)
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e20
              | exact resolve b7e20 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e35 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
              intro X0
              first
              | (have i₁ := b7e14 X0 x y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                 have i₂ := b7e14 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e40 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
              intro X0 X3
              first
              | (have i₁ := b7e37 X0 x x X3
                 have i₂ := b7e14 X0 x x
                 grind)
              | exact superpose b7e14 b7e37
              | exact resolve b7e37 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e37
            have b7e66 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x (M.op y y)) = (k (M.op x (M.op y y)) X0) := by
              intro X0
              first
              | (have i₁ := b7e17 (M.op x (M.op y y)) X0
                 have i₂ := b7e35 X0
                 grind)
              | exact superpose b7e35 b7e17
              | (have j0 := b7e17 (M.op x (M.op y y)) X0
                 grind)
              | (have r₁ := b7e17 (M.op x (M.op y y)) X0
                 have r₂ := b7e35 X0
                 grind)
              | exact resolve b7e17 b7e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e35
            have b7e69 : ∀ X0 : G, (M.op x (M.op y y)) = (k (M.op x (M.op y y)) X0) := by
              intro X0
              first
              | (have j0 := b7e66 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e66
            have b7e71 : ∀ X0 : G, x = (k x X0) := by
              intro X0
              first
              | (have i₁ := b7e69 X0
                 have i₂ := b7e40 y x
                 grind)
              | (have i₁ := b7e69 X0
                 have i₂ := b7e40 X0 (M.op x (M.op y y))
                 grind)
              | exact superpose b7e40 b7e69
              | exact resolve b7e69 b7e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40 b7e69
            have b7e96 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b7e33 X0 x
                 have i₂ := b7e71 (τ X0)
                 grind)
              | exact superpose b7e71 b7e33
              | exact resolve b7e33 b7e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e33 b7e71
            have b7e127 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b7e19 (σ x) X0
                 have i₂ := b7e96 X0
                 grind)
              | exact superpose b7e96 b7e19
              | (have j0 := b7e19 (σ x) X0
                 grind)
              | exact resolve b7e19 b7e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e96
            have b7e129 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have j0 := b7e127 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e127
            have b7e664 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e24
                 have i₂ := b7e129 (σ y)
                 grind)
              | exact superpose b7e129 b7e24
              | (have j1 := b7e129 (σ y)
                 grind)
              | (have r₁ := b7e24
                 have r₂ := b7e129 (σ y)
                 grind)
              | exact resolve b7e24 b7e129
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e129
            have b7e676 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear b7e664
            have b7e678 : False := by grind
            exact b7e678
          · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op y x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : y ≠ y ∨ x = (k x y) := by
              first
              | (have i₁ := b8e17 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 x y
                 grind)
              | (have r₁ := b8e17 x y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e28 : x = (k x y) := by grind
            clear b8e27
            have b8e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
            have b8e128 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b8e53 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e53
            have b8e679 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b8e128 y x
                 have i₂ := b8e28
                 grind)
              | exact superpose b8e28 b8e128
              | (have j0 := b8e128 y x
                 grind)
              | exact resolve b8e128 b8e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28 b8e128
            have b8e682 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
            clear b8e679
            have b8e693 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have r₁ := b8e682
                 have r₂ := b8e24
                 grind)
              | exact resolve b8e682 b8e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e682
            have b8e699 : False := by grind
            exact b8e699
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op y x) := by grind
          have b9e22 : x = (M.op y x) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : x ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e29 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ y)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e30 : (σ x) = (k (σ x) (σ y)) := by grind
          clear b9e29
          have b9e32 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b9e30
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e30
            | exact resolve b9e30 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30
          have b9e37 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e32
               grind)
            | exact superpose b9e32 b9e14
            | exact resolve b9e14 b9e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32
          have b9e38 : x = (k x y) := by
            first
            | (have i₁ := b9e37
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e37
            | exact resolve b9e37 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e37
          have b9e52 : x ≠ x ∨ x = y ∨ y = (k x y) := by
            first
            | (have i₁ := b9e17 x y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x y
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e53 : x = y ∨ y = (k x y) := by grind
          clear b9e52
          have b9e54 : y = (k x y) := by
            first
            | (have r₁ := b9e53
               have r₂ := b9e25
               grind)
            | exact resolve b9e53 b9e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e53
          have b9e55 : x = y := by
            first
            | (have i₁ := b9e54
               have i₂ := b9e38
               grind)
            | exact superpose b9e38 b9e54
            | exact resolve b9e54 b9e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e38 b9e54
          have b9e56 : False := by grind
          exact b9e56
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e23 : x = (M.op y x) := by grind
            have b10e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : x ≠ (M.op x y) := by grind
            have b10e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : x ≠ y := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e25
              | exact resolve b10e25 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e32 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e33 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b10e32
            have b10e34 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b10e33
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e33
              | exact resolve b10e33 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e35 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e34
                 grind)
              | exact superpose b10e34 b10e15
              | exact resolve b10e15 b10e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34
            have b10e36 : x = (k x y) := by
              first
              | (have i₁ := b10e35
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e35
              | exact resolve b10e35 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e35
            have b10e62 : x ≠ x ∨ x = y ∨ y = (k x y) := by
              first
              | (have i₁ := b10e18 x y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e18
              | (have j0 := b10e18 x y
                 grind)
              | (have r₁ := b10e18 x y
                 have r₂ := b10e23
                 grind)
              | exact resolve b10e18 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e63 : x = y ∨ y = (k x y) := by grind
            clear b10e62
            have b10e65 : y = (k x y) := by
              first
              | (have r₁ := b10e63
                 have r₂ := b10e27
                 grind)
              | exact resolve b10e63 b10e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e63
            have b10e68 : x = y := by
              first
              | (have i₁ := b10e36
                 have i₂ := b10e65
                 grind)
              | exact superpose b10e65 b10e36
              | exact resolve b10e36 b10e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e36 b10e65
            have b10e70 : False := by grind
            exact b10e70
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op y x) := by grind
            have b11e23 : x = (M.op y x) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : x ≠ y := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e22
              | exact resolve b11e22 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e29 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b11e17 (σ x) (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b11e17 (σ x) (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e30 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b11e29
            have b11e31 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e30
              | exact resolve b11e30 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e31
                 grind)
              | exact superpose b11e31 b11e15
              | exact resolve b11e15 b11e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e33 : x = (k x y) := by
              first
              | (have i₁ := b11e32
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e32
              | exact resolve b11e32 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e61 : x ≠ x ∨ x = y ∨ y = (k x y) := by
              first
              | (have i₁ := b11e18 x y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x y
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e62 : x = y ∨ y = (k x y) := by grind
            clear b11e61
            have b11e63 : y = (k x y) := by
              first
              | (have r₁ := b11e62
                 have r₂ := b11e27
                 grind)
              | exact resolve b11e62 b11e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e62
            have b11e65 : x = y := by
              first
              | (have i₁ := b11e33
                 have i₂ := b11e63
                 grind)
              | exact superpose b11e63 b11e33
              | exact resolve b11e33 b11e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33 b11e63
            have b11e67 : False := by grind
            exact b11e67
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e25 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b12e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e29 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e37 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e14 X0 (σ y) (σ x)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                 have i₂ := b12e14 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e43 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
              intro X0 X3
              first
              | (have i₁ := b12e40 X0 x x X3
                 have i₂ := b12e14 X0 x x
                 grind)
              | exact superpose b12e14 b12e40
              | exact resolve b12e40 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e106 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b12e37 X0
                 have i₂ := b12e43 (σ x) (σ y)
                 grind)
              | exact superpose b12e43 b12e37
              | exact resolve b12e37 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e37 b12e43
            have b12e119 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e29
                 have i₂ := b12e106 (σ x)
                 grind)
              | exact superpose b12e106 b12e29
              | (have r₁ := b12e29
                 have r₂ := b12e106 (σ x)
                 grind)
              | exact resolve b12e29 b12e106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29 b12e106
            have b12e120 : False := by grind
            exact b12e120
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b13e24 : x = (M.op y x) := by grind
              have b13e27 : x ≠ (M.op x y) := by grind
              have b13e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : x ≠ y := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e27
                | exact resolve b13e27 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e44 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
                intro X0
                first
                | (have i₁ := b13e15 X0 x y
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e46 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b13e15 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                   have i₂ := b13e15 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e49 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b13e46 X0 x x X3
                   have i₂ := b13e15 X0 x x
                   grind)
                | exact superpose b13e15 b13e46
                | exact resolve b13e46 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e46
              have b13e80 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b13e44 X0
                   have i₂ := b13e49 y x
                   grind)
                | exact superpose b13e49 b13e44
                | exact resolve b13e44 b13e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e44 b13e49
              have b13e94 : x = y := by
                first
                | (have i₁ := b13e24
                   have i₂ := b13e80 y
                   grind)
                | exact superpose b13e80 b13e24
                | exact resolve b13e24 b13e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e80
              have b13e96 : False := by grind
              exact b13e96
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b14e24 : x = (M.op y x) := by grind
              have b14e27 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e35 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e15 X0 y x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e38 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                   have i₂ := b14e15 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e41 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b14e38 X0 x x X3
                   have i₂ := b14e15 X0 x x
                   grind)
                | exact superpose b14e15 b14e38
                | exact resolve b14e38 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e38
              have b14e64 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b14e35 X0
                   have i₂ := b14e41 x y
                   grind)
                | exact superpose b14e41 b14e35
                | exact resolve b14e35 b14e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e35 b14e41
              have b14e83 : x ≠ x := by
                first
                | (have i₁ := b14e27
                   have i₂ := b14e64 x
                   grind)
                | exact superpose b14e64 b14e27
                | (have r₁ := b14e27
                   have r₂ := b14e64 x
                   grind)
                | exact resolve b14e27 b14e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e64
              have b14e84 : False := by grind
              exact b14e84
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : y ≠ (M.op y x) := by grind
            have b15e23 : x = (M.op y x) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e22
              | exact resolve b15e22 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e51 : x ≠ x ∨ x = y ∨ y = (k x y) := by
              first
              | (have i₁ := b15e18 x y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e18
              | (have j0 := b15e18 x y
                 grind)
              | (have r₁ := b15e18 x y
                 have r₂ := b15e23
                 grind)
              | exact resolve b15e18 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e52 : x = y ∨ y = (k x y) := by grind
            clear b15e51
            have b15e53 : y = (k x y) := by
              first
              | (have r₁ := b15e52
                 have r₂ := b15e27
                 grind)
              | exact resolve b15e52 b15e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27 b15e52
            have b15e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 X0
                 have i₂ := b15e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e146 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b15e57 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e57
            have b15e759 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b15e146 y x
                 have i₂ := b15e53
                 grind)
              | exact superpose b15e53 b15e146
              | (have j0 := b15e146 y x
                 grind)
              | exact resolve b15e146 b15e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e53 b15e146
            have b15e764 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
            clear b15e759
            have b15e767 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have r₁ := b15e764
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e764 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e764
            have b15e775 : False := by grind
            exact b15e775
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b16e24 : x = (M.op y x) := by grind
              have b16e27 : x ≠ (M.op x y) := by grind
              have b16e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : x ≠ y := by
                first
                | (have i₁ := b16e27
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e27
                | exact resolve b16e27 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e40 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
                intro X0
                first
                | (have i₁ := b16e15 X0 y x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e43 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                   have i₂ := b16e15 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e46 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b16e43 X0 x x X3
                   have i₂ := b16e15 X0 x x
                   grind)
                | exact superpose b16e15 b16e43
                | exact resolve b16e43 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e43
              have b16e73 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b16e40 X0
                   have i₂ := b16e46 x y
                   grind)
                | exact superpose b16e46 b16e40
                | exact resolve b16e40 b16e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e40 b16e46
              have b16e87 : x = y := by
                first
                | (have i₁ := b16e28
                   have i₂ := b16e73 x
                   grind)
                | exact superpose b16e73 b16e28
                | exact resolve b16e28 b16e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e73
              have b16e89 : False := by grind
              exact b16e89
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b17e24 : x = (M.op y x) := by grind
              have b17e27 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e33 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
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
              have b17e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                   have i₂ := b17e15 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e38 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b17e35 X0 x x X3
                   have i₂ := b17e15 X0 x x
                   grind)
                | exact superpose b17e15 b17e35
                | exact resolve b17e35 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35
              have b17e57 : ∀ X0 : G, (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b17e33 X0
                   have i₂ := b17e38 x y
                   grind)
                | exact superpose b17e38 b17e33
                | exact resolve b17e33 b17e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e33 b17e38
              have b17e76 : x ≠ x := by
                first
                | (have i₁ := b17e27
                   have i₂ := b17e57 x
                   grind)
                | exact superpose b17e57 b17e27
                | (have r₁ := b17e27
                   have r₂ := b17e57 x
                   grind)
                | exact resolve b17e27 b17e57
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57
              have b17e77 : False := by grind
              exact b17e77
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op y x) := by grind
          have b18e22 : x ≠ (M.op y x) := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b18e16 (σ x) (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e16
            | (have j0 := b18e16 (σ x) (σ y)
               grind)
            | (have r₁ := b18e16 (σ x) (σ y)
               have r₂ := b18e23
               grind)
            | exact resolve b18e16 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : (σ x) = (k (σ x) (σ y)) := by grind
          clear b18e27
          have b18e30 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e28
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e28
            | exact resolve b18e28 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28
          have b18e35 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e30
               grind)
            | exact superpose b18e30 b18e14
            | exact resolve b18e14 b18e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30
          have b18e36 : x = (k x y) := by
            first
            | (have i₁ := b18e35
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e35
            | exact resolve b18e35 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e61 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e36
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e36
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e36 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e65 : x = (M.op y x) ∨ y = (M.op y x) := by grind
          clear b18e61
          have b18e69 : y = (M.op y x) := by
            first
            | (have r₁ := b18e65
               have r₂ := b18e22
               grind)
            | exact resolve b18e65 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e65
          have b18e72 : False := by grind
          exact b18e72
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op y x) := by grind
            have b19e23 : x ≠ (M.op y x) := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e17
              | (have j0 := b19e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b19e17 (σ x) (σ y)
                 have r₂ := b19e24
                 grind)
              | exact resolve b19e17 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e31 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b19e30
            have b19e32 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e31
              | exact resolve b19e31 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e37 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e32
                 grind)
              | exact superpose b19e32 b19e15
              | exact resolve b19e15 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e38 : x = (k x y) := by
              first
              | (have i₁ := b19e37
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e37
              | exact resolve b19e37 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e37
            have b19e57 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e38
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e38
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e38 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e38
            have b19e61 : x = (M.op y x) ∨ y = (M.op y x) := by grind
            clear b19e57
            have b19e65 : y = (M.op y x) := by
              first
              | (have r₁ := b19e61
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e61 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e61
            have b19e68 : False := by grind
            exact b19e68
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y x) := by grind
            have b20e23 : x ≠ (M.op y x) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ x) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b20e17 (σ x) (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e28 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b20e27
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
            have b20e30 : (k x y) = (τ (σ x)) := by
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
            have b20e31 : x = (k x y) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e30
              | exact resolve b20e30 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e66 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e31
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e31 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e68 : x = (M.op y x) ∨ y = (M.op y x) := by grind
            clear b20e66
            have b20e73 : y = (M.op y x) := by
              first
              | (have r₁ := b20e68
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e68 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e68
            have b20e76 : False := by grind
            exact b20e76
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : y ≠ (M.op y x) := by grind
            have b21e23 : x ≠ (M.op y x) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e24
              | exact resolve b21e24 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e51 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b21e52 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b21e51
            have b21e53 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e52
                 have r₂ := b21e27
                 grind)
              | exact resolve b21e52 b21e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e27 b21e52
            have b21e54 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b21e53
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e53
              | exact resolve b21e53 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e53
            have b21e57 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e54
                 grind)
              | exact superpose b21e54 b21e15
              | exact resolve b21e15 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e54
            have b21e58 : y = (k x y) := by
              first
              | (have i₁ := b21e57
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e57
              | exact resolve b21e57 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e57
            have b21e71 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e58
                 grind)
              | exact superpose b21e58 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e58
            have b21e72 : y = (M.op y x) ∨ x = (M.op y x) := by grind
            clear b21e71
            have b21e74 : x = (M.op y x) := by
              first
              | (have r₁ := b21e72
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e72 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e72
            have b21e76 : False := by grind
            exact b21e76
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b22e23 : y ≠ (M.op y x) := by grind
              have b22e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e36 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
                intro X0
                first
                | (have i₁ := b22e15 X0 x y
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e39 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                   have i₂ := b22e15 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e42 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b22e39 X0 x x X3
                   have i₂ := b22e15 X0 x x
                   grind)
                | exact superpose b22e15 b22e39
                | exact resolve b22e39 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e39
              have b22e74 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b22e36 X0
                   have i₂ := b22e42 y x
                   grind)
                | exact superpose b22e42 b22e36
                | exact resolve b22e36 b22e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e36 b22e42
              have b22e97 : y ≠ y := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e74 y
                   grind)
                | exact superpose b22e74 b22e23
                | (have r₁ := b22e23
                   have r₂ := b22e74 y
                   grind)
                | exact resolve b22e23 b22e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e74
              have b22e98 : False := by grind
              exact b22e98
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : y ≠ (M.op y x) := by grind
              have b23e24 : x ≠ (M.op y x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b23e25
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e25
                | exact resolve b23e25 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e48 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b23e19 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e19
                | (have j0 := b23e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b23e19 (σ x) (σ y)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e19 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e49 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
              clear b23e48
              have b23e50 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e49
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e49 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29 b23e49
              have b23e51 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e50
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e50
                | exact resolve b23e50 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e50
              have b23e54 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e51
                   grind)
                | exact superpose b23e51 b23e16
                | exact resolve b23e16 b23e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e51
              have b23e55 : y = (k x y) := by
                first
                | (have i₁ := b23e54
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e54
                | exact resolve b23e54 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e54
              have b23e64 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e55
                   grind)
                | exact superpose b23e55 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e55
              have b23e65 : y = (M.op y x) ∨ x = (M.op y x) := by grind
              clear b23e64
              have b23e67 : x = (M.op y x) := by
                first
                | (have r₁ := b23e65
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e65 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e65
              have b23e69 : False := by grind
              exact b23e69
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e21
              | exact resolve b24e21 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e28 : x ≠ x ∨ y = (k y x) := by
              first
              | (have i₁ := b24e17 y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e17
              | (have j0 := b24e17 y x
                 grind)
              | (have r₁ := b24e17 y x
                 have r₂ := b24e26
                 grind)
              | exact resolve b24e17 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e29 : y = (k y x) := by grind
            clear b24e28
            have b24e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
            have b24e129 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b24e54 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e54
            have b24e680 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e129 x y
                 have i₂ := b24e29
                 grind)
              | exact superpose b24e29 b24e129
              | (have j0 := b24e129 x y
                 grind)
              | exact resolve b24e129 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e129
            have b24e683 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
            clear b24e680
            have b24e694 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b24e683
                 have r₂ := b24e27
                 grind)
              | exact resolve b24e683 b24e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e683
            have b24e710 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b24e27
                 have i₂ := b24e694
                 grind)
              | exact superpose b24e694 b24e27
              | exact resolve b24e27 b24e694
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e27
            have b24e713 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b24e18 (σ y) (σ x)
                 have i₂ := b24e694
                 grind)
              | exact superpose b24e694 b24e18
              | (have j0 := b24e18 (σ y) (σ x)
                 grind)
              | (have r₁ := b24e18 (σ y) (σ x)
                 have r₂ := b24e694
                 grind)
              | exact resolve b24e18 b24e694
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e694
            have b24e716 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
            clear b24e713
            have b24e719 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b24e716
                 have i₂ := b24e20 y x
                 grind)
              | exact superpose b24e20 b24e716
              | exact resolve b24e716 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e716
            have b24e723 : (σ x) = (σ (k y x)) := by
              first
              | (have r₁ := b24e719
                 have r₂ := b24e710
                 grind)
              | exact resolve b24e719 b24e710
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e719
            have b24e724 : (σ x) = (σ y) := by
              first
              | (have i₁ := b24e723
                 have i₂ := b24e29
                 grind)
              | exact superpose b24e29 b24e723
              | exact resolve b24e723 b24e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e29 b24e723
            have b24e725 : False := by grind
            exact b24e725
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b25e23 : y ≠ (M.op y x) := by grind
              have b25e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e34 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e15 X0 x y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e36 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                   have i₂ := b25e15 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b25e36 X0 x x X3
                   have i₂ := b25e15 X0 x x
                   grind)
                | exact superpose b25e15 b25e36
                | exact resolve b25e36 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e36
              have b25e58 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b25e34 X0
                   have i₂ := b25e39 y x
                   grind)
                | exact superpose b25e39 b25e34
                | exact resolve b25e34 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e34 b25e39
              have b25e77 : y ≠ y := by
                first
                | (have i₁ := b25e23
                   have i₂ := b25e58 y
                   grind)
                | exact superpose b25e58 b25e23
                | (have r₁ := b25e23
                   have r₂ := b25e58 y
                   grind)
                | exact resolve b25e23 b25e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e58
              have b25e78 : False := by grind
              exact b25e78
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e27 : x ≠ (M.op x y) := by grind
              have b26e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 (τ X0) X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e21
                | exact resolve b26e21 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e32 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
                   have i₂ := b26e15 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e35 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b26e32 X0 x x X3
                   have i₂ := b26e15 X0 x x
                   grind)
                | exact superpose b26e15 b26e32
                | exact resolve b26e32 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e32
              have b26e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
              have b26e57 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k (τ X0) X1)
                   have i₂ := b26e29 X0 X1
                   grind)
                | exact superpose b26e29 b26e16
                | exact resolve b26e16 b26e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29
              have b26e68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e57 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e57
                | exact resolve b26e57 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e57
              have b26e113 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e49 x y
                   grind)
                | exact superpose b26e49 b26e22
                | (have j1 := b26e49 x y
                   grind)
                | exact resolve b26e22 b26e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e120 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have j0 := b26e49 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49
              have b26e663 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e120 (τ X1) (τ X0)
                   have i₂ := b26e68 X1 X0
                   grind)
                | exact superpose b26e68 b26e120
                | (have j0 := b26e120 (τ X1) (τ X0)
                   grind)
                | exact resolve b26e120 b26e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68 b26e120
              have b26e683 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e663 X0 X1
                   have i₂ := b26e17 (k X0 X1)
                   grind)
                | exact superpose b26e17 b26e663
                | (have j0 := b26e663 X0 X1
                   grind)
                | exact resolve b26e663 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e663
              have b26e688 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e683 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e683
                | (have j0 := b26e683 X0 X1
                   grind)
                | exact resolve b26e683 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e683
              have b26e691 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e688 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e688
                | (have j0 := b26e688 X0 X1
                   grind)
                | exact resolve b26e688 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e688
              have b26e692 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e691 X0 X1
                   have i₂ := b26e17 X1
                   grind)
                | exact superpose b26e17 b26e691
                | (have j0 := b26e691 X0 X1
                   grind)
                | exact resolve b26e691 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e691
              have b26e693 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e692 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e692
                | (have j0 := b26e692 X0 X1
                   grind)
                | exact resolve b26e692 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e692
              have b26e694 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e693 X0 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e693
                | (have j0 := b26e693 X0 X1
                   grind)
                | exact resolve b26e693 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e693
              have b26e848 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e113
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e113
                | (have j1 := b26e20 (σ y) (σ x)
                   grind)
                | exact resolve b26e113 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e113
              have b26e849 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
              clear b26e848
              have b26e850 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b26e849
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e849 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e849
              have b26e851 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e850
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e850 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e850
              have b26e1423 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e15 X0 (σ x) (σ y)
                   have i₂ := b26e851
                   grind)
                | exact superpose b26e851 b26e15
                | exact resolve b26e15 b26e851
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e851
              have b26e1427 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e1423 X0
                   have i₂ := b26e35 (σ y) (σ x)
                   grind)
                | (have i₁ := b26e1423 X0
                   have i₂ := b26e35 X0 (M.op (σ x) (M.op (σ y) (σ y)))
                   grind)
                | exact superpose b26e35 b26e1423
                | exact resolve b26e1423 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e1423
              have b26e1698 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e25
                   have i₂ := b26e1427 (σ y)
                   grind)
                | exact superpose b26e1427 b26e25
                | (have r₁ := b26e25
                   have r₂ := b26e1427 (σ y)
                   grind)
                | exact resolve b26e25 b26e1427
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1427
              have b26e1705 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear b26e1698
              have b26e1828 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b26e18 (σ y) (σ x)
                   have i₂ := b26e1705
                   grind)
                | exact superpose b26e1705 b26e18
                | (have j0 := b26e18 (σ y) (σ x)
                   grind)
                | (have r₁ := b26e18 (σ y) (σ x)
                   have r₂ := b26e1705
                   grind)
                | exact resolve b26e18 b26e1705
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1705
              have b26e1829 : (σ y) = (k (σ y) (σ x)) := by grind
              clear b26e1828
              have b26e1830 : (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e1829
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e1829
                | exact resolve b26e1829 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1829
              have b26e2019 : (k y x) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (k y x)
                   have i₂ := b26e1830
                   grind)
                | exact superpose b26e1830 b26e16
                | exact resolve b26e16 b26e1830
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1830
              have b26e2059 : y = (k y x) := by
                first
                | (have i₁ := b26e2019
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e2019
                | exact resolve b26e2019 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2019
              have b26e2116 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e694 y x
                   have i₂ := b26e2059
                   grind)
                | exact superpose b26e2059 b26e694
                | (have j0 := b26e694 y x
                   grind)
                | (have r₁ := b26e694 y x
                   have r₂ := b26e2059
                   grind)
                | exact resolve b26e694 b26e2059
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e694 b26e2059
              have b26e2118 : y = (M.op x y) ∨ x = (M.op x y) := by grind
              clear b26e2116
              have b26e2123 : x = (M.op x y) := by
                first
                | (have r₁ := b26e2118
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e2118 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2118
              have b26e2127 : False := by grind
              exact b26e2127
