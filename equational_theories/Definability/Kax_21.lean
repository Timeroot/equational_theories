import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4456`: `x ◇ (y ◇ x) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4456 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4456 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4456.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
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
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
      have b0e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X1 X3
           have i₂ := b0e11 X2 X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 (M.op X1 X2) X2
           have i₂ := b0e11 X2 X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
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
      have b0e40 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
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
      have b0e41 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e40 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x y
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e56 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e56
        | exact resolve b0e56 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e56
      have b0e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e67 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X2 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e100 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e57 X0
           grind)
        | exact superpose b0e57 b0e11
        | exact resolve b0e11 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e143 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X0 (σ x) X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e178 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e100 x
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e100
        | exact resolve b0e100 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e201 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e39 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e39
        | exact resolve b0e39 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e268 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op X0 (σ x))) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e35 (M.op x X0)
           have i₂ := b0e11 (σ x) X0 x
           grind)
        | exact superpose b0e11 b0e35
        | exact resolve b0e35 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e290 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) := by
        intro X0
        first
        | (have i₁ := b0e268 X0
           have i₂ := b0e11 (σ x) (M.op X0 (σ x)) (σ x)
           grind)
        | exact superpose b0e11 b0e268
        | exact resolve b0e268 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e268
      have b0e292 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b0e290 x
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e290
        | exact resolve b0e290 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e290
      have b0e645 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ x)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X1 (σ x) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e37
        | exact resolve b0e37 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e806 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e645 X0 x
           have i₂ := b0e143 (M.op x (σ x)) X0
           grind)
        | exact superpose b0e143 b0e645
        | exact resolve b0e645 b0e143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e143 b0e645
      have b0e1367 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e67 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e2361 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X1) (σ X0)
           have i₂ := b0e62 X1 X0
           grind)
        | exact superpose b0e62 b0e15
        | (have j0 := b0e15 (σ X1) (σ X0)
           have j1 := b0e62 X1 X0
           grind)
        | (have r₁ := b0e15 (σ X1) (σ X1)
           have r₂ := b0e62 X1 X1
           grind)
        | (have r₁ := b0e15 (σ X0) (σ X1)
           have r₂ := b0e62 X0 X1
           grind)
        | exact resolve b0e15 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e2384 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e2361 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2361
      have b0e2385 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e2384 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2384
      have b0e2401 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2385 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e2385
        | (have j0 := b0e2385 X0 X1
           grind)
        | exact resolve b0e2385 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2385
      have b0e97576 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1367 X0 (σ y)
           have i₂ := b0e806 (σ y)
           grind)
        | exact superpose b0e806 b0e1367
        | (have j0 := b0e1367 X0 (σ y)
           grind)
        | (have r₁ := b0e1367 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) (σ y)
           have r₂ := b0e806 (M.op (σ y) (σ y))
           grind)
        | (have r₁ := b0e1367 (M.op (σ y) (σ y)) (σ y)
           have r₂ := b0e806 (σ y)
           grind)
        | exact resolve b0e1367 b0e806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e806
      have b0e97578 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1367 X0 y
           have i₂ := b0e100 y
           grind)
        | exact superpose b0e100 b0e1367
        | (have j0 := b0e1367 X0 y
           grind)
        | (have r₁ := b0e1367 (M.op (M.op y y) (M.op y (M.op y y))) y
           have r₂ := b0e100 (M.op y y)
           grind)
        | (have r₁ := b0e1367 (M.op y y) y
           have r₂ := b0e100 y
           grind)
        | exact resolve b0e1367 b0e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100 b0e1367
      have b0e97697 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b0e97578 X0
           have j1 := b0e16 y X0
           grind)
        | (have r₁ := b0e97578 (k y y)
           have r₂ := b0e16 y y
           grind)
        | (have r₁ := b0e97578 x
           have r₂ := b0e16 y x
           grind)
        | (have r₁ := b0e97578 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op y y)
           grind)
        | exact resolve b0e97578 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97578
      have b0e97699 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b0e97576 X0
           have j1 := b0e16 (σ y) X0
           grind)
        | (have r₁ := b0e97576 (k (σ y) (σ y))
           have r₂ := b0e16 (σ y) (σ y)
           grind)
        | (have r₁ := b0e97576 x
           have r₂ := b0e16 (σ y) x
           grind)
        | (have r₁ := b0e97576 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op (σ y) (σ y))
           grind)
        | exact resolve b0e97576 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97576
      have b0e99574 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e17 y X0
           have i₂ := b0e97699 (σ X0)
           grind)
        | exact superpose b0e97699 b0e17
        | (have j1 := b0e97699 (σ X0)
           grind)
        | exact resolve b0e17 b0e97699
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97699
      have b0e232055 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        grind
      clear b0e2401
      have b0e232261 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e232055 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e232055
        | (have j0 := b0e232055 X0 X1
           grind)
        | exact resolve b0e232055 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232055
      have b0e232262 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e232261 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232261
      have b0e236269 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e232262 X0 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e232262
        | exact resolve b0e232262 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e236293 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e201
           have i₂ := b0e232262 x y
           grind)
        | exact superpose b0e232262 b0e201
        | (have j1 := b0e232262 x y
           grind)
        | exact resolve b0e201 b0e232262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232262
      have b0e236430 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e236269 X0 X1
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e236269
        | (have j0 := b0e236269 X0 X1
           grind)
        | exact resolve b0e236269 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236269
      have b0e236434 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e236430 X0 X1
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e236430
        | (have j0 := b0e236430 X0 X1
           grind)
        | exact resolve b0e236430 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e236430
      have b0e256653 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e236434 X0 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e236434
        | exact resolve b0e236434 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236434
      have b0e258838 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e26 X1 X0
           have i₂ := b0e256653 (τ X1) X0
           grind)
        | exact superpose b0e256653 b0e26
        | (have j1 := b0e256653 (τ X1) X0
           grind)
        | exact resolve b0e26 b0e256653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26
      have b0e258898 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e256653 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e256653
      have b0e261579 : y ≠ (M.op x y) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e258898 y x
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e258898
        | (have j0 := b0e258898 y x
           grind)
        | exact resolve b0e258898 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e258898
      have b0e312475 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e258838 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e258838
        | exact resolve b0e258838 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e258838
      have b0e312501 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e312475 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e312475
        | (have j0 := b0e312475 X0 X1
           grind)
        | exact resolve b0e312475 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e312475
      have b0e441377 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e236293
           grind)
        | exact superpose b0e236293 b0e18
        | exact resolve b0e18 b0e236293
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236293
      have b0e445426 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e441377
           have i₂ := b0e97697 x
           grind)
        | exact superpose b0e97697 b0e441377
        | (have j1 := b0e97697 x
           grind)
        | exact resolve b0e441377 b0e97697
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97697
      have b0e445428 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e441377
           have i₂ := b0e312501 x y
           grind)
        | exact superpose b0e312501 b0e441377
        | (have j1 := b0e312501 x y
           grind)
        | exact resolve b0e441377 b0e312501
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e312501 b0e441377
      have b0e445429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e445428
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e445428
        | exact resolve b0e445428 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445428
      have b0e445430 : (σ y) = (σ (M.op y x)) ∨ y = (k y x) := by grind
      clear b0e445429
      have b0e445433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e445426
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e445426
        | exact resolve b0e445426 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445426
      have b0e445434 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
      clear b0e445433
      have b0e445435 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e445430
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e445430
        | exact resolve b0e445430 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445430
      have b0e445437 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e445434
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e445434
        | exact resolve b0e445434 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e445434
      have b0e464132 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e445435
           grind)
        | exact superpose b0e445435 b0e12
        | exact resolve b0e12 b0e445435
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445435
      have b0e464145 : y = (M.op x y) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e464132
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e464132
        | exact resolve b0e464132 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e464132
      have b0e464146 : y = (k y x) := by
        first
        | (have r₁ := b0e464145
           have r₂ := b0e261579
           grind)
        | exact resolve b0e464145 b0e261579
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e261579 b0e464145
      have b0e651907 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e201
           have i₂ := b0e99574 x
           grind)
        | exact superpose b0e99574 b0e201
        | (have j1 := b0e99574 x
           grind)
        | exact resolve b0e201 b0e99574
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e201 b0e99574
      have b0e651918 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e651907
           have i₂ := b0e464146
           grind)
        | exact superpose b0e464146 b0e651907
        | exact resolve b0e651907 b0e464146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e464146 b0e651907
      have b0e656386 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e651918
           grind)
        | exact superpose b0e651918 b0e18
        | exact resolve b0e18 b0e651918
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e651918
      have b0e666709 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e656386
           have i₂ := b0e445437
           grind)
        | exact superpose b0e445437 b0e656386
        | (have r₁ := b0e656386
           have r₂ := b0e445437
           grind)
        | exact resolve b0e656386 b0e445437
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445437 b0e656386
      have b0e666710 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e666709
      have b0e668958 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e292
           have i₂ := b0e666710
           grind)
        | exact superpose b0e666710 b0e292
        | exact resolve b0e292 b0e666710
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e292 b0e666710
      have b0e669057 : x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e668958
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e668958
        | exact resolve b0e668958 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e668958
      have b0e673911 : x = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e178
           have i₂ := b0e669057
           grind)
        | exact superpose b0e669057 b0e178
        | exact resolve b0e178 b0e669057
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e178 b0e669057
      have b0e674219 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e673911
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e673911
        | exact resolve b0e673911 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e673911
      have b0e676529 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e674219
           grind)
        | exact superpose b0e674219 b0e12
        | exact resolve b0e12 b0e674219
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e674219
      have b0e676579 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e676529
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e676529
        | exact resolve b0e676529 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e676529
      have b0e676580 : x = y := by grind
      clear b0e676579
      have b0e677994 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e676580
           grind)
        | exact superpose b0e676580 b0e18
        | exact resolve b0e18 b0e676580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e676580
      have b0e678259 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e677994
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e677994
        | exact resolve b0e677994 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e677994
      have b0e678283 : False := by grind
      exact b0e678283
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
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
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b1e29 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 X1 X3
             have i₂ := b1e12 X2 X1 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X3 (M.op X1 X2) X2
             have i₂ := b1e12 X2 X1 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 X0 (M.op x X1)
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e115 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        clear b1e26
        have b1e165 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 X0 (σ x) X1 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e30
          | exact resolve b1e30 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e379 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 (M.op X2 X1) X1
             have i₂ := b1e32 X1 X2 X0
             grind)
          | exact superpose b1e32 b1e12
          | exact resolve b1e12 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e623 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e115
        have b1e636 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e623 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e623
          | exact resolve b1e623 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e623
        have b1e658 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e31 X1 (σ y) (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e31
          | exact resolve b1e31 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e774 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e29 (M.op (M.op x X0) X1)
             have i₂ := b1e31 x X0 X1 (σ y)
             grind)
          | exact superpose b1e31 b1e29
          | exact resolve b1e29 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e31
        have b1e777 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e774 X0 X1
             have i₂ := b1e12 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
             grind)
          | exact superpose b1e12 b1e774
          | exact resolve b1e774 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774
        have b1e819 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e658 X0 x
             have i₂ := b1e165 (M.op x (σ y)) X0
             grind)
          | exact superpose b1e165 b1e658
          | exact resolve b1e658 b1e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e165 b1e658
        have b1e825 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b1e777 x x
             have i₂ := b1e379 (σ x) (σ y) (M.op x x)
             grind)
          | exact superpose b1e379 b1e777
          | exact resolve b1e777 b1e379
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e379 b1e777
        have b1e841 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e825
             have i₂ := b1e819 (σ x)
             grind)
          | exact superpose b1e819 b1e825
          | exact resolve b1e825 b1e819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e819 b1e825
        have b1e844 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e841
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e841
          | exact resolve b1e841 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e841
        have b1e845 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e844
             grind)
          | exact superpose b1e844 b1e19
          | exact resolve b1e19 b1e844
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e844
        have b1e2242 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e59 x x
             grind)
          | exact superpose b1e59 b1e21
          | (have j1 := b1e59 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e59 x y
             grind)
          | exact resolve b1e21 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e2343 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e2242
        have b1e22005 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2343
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e2343
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e2343 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2343
        have b1e22006 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e22005
        have b1e22007 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e22006
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e22006
          | exact resolve b1e22006 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e22006
        have b1e22008 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e22007
        have b1e22014 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e22008
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e22008
          | exact resolve b1e22008 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e22008
        have b1e23059 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e636 x
             have i₂ := b1e22014
             grind)
          | exact superpose b1e22014 b1e636
          | exact resolve b1e636 b1e22014
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e636 b1e22014
        have b1e23120 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e23059
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e23059
          | exact resolve b1e23059 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23059
        have b1e24100 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e23120
             grind)
          | exact superpose b1e23120 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e23120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23120
        have b1e24101 : x = (M.op x x) ∨ x = y := by grind
        clear b1e24100
        have b1e24110 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e24101
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e24101
          | exact resolve b1e24101 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24101
        have b1e24111 : x = y := by grind
        clear b1e24110
        have b1e25455 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e845
             have i₂ := b1e24111
             grind)
          | exact superpose b1e24111 b1e845
          | exact resolve b1e845 b1e24111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e845
        have b1e25459 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e25455
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e25455
          | exact resolve b1e25455 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25455
        have b1e25469 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e25459
             have i₂ := b1e24111
             grind)
          | exact superpose b1e24111 b1e25459
          | exact resolve b1e25459 b1e24111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24111 b1e25459
        have b1e25470 : False := by grind
        exact b1e25470
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
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
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X1 X3
             have i₂ := b2e12 X2 X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 (M.op X1 X2) X2
             have i₂ := b2e12 X2 X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e109 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e895 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e109
        have b2e908 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e895 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e895
          | exact resolve b2e895 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e895
        have b2e940 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e58 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e941 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e940
             have r₂ := b2e22
             grind)
          | exact resolve b2e940 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e940
        have b2e942 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e941
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e941
          | exact resolve b2e941 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e941
        have b2e943 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e942
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e942
          | exact resolve b2e942 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e942
        have b2e953 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e29 X0 (σ y) X1 (σ x)
             have i₂ := b2e943
             grind)
          | exact superpose b2e943 b2e29
          | exact resolve b2e29 b2e943
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e1857 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e53 x x
             grind)
          | exact superpose b2e53 b2e21
          | (have j1 := b2e53 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e53 x y
             grind)
          | exact resolve b2e21 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e1945 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1857
        have b2e2152 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (M.op X2 X1) (σ y)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31 X2 X1 (σ y) X0
             have i₂ := b2e953 X1 X0
             grind)
          | exact superpose b2e953 b2e31
          | exact resolve b2e31 b2e953
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e2208 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e2152 X0 x x
             have i₂ := b2e953 (M.op x x) X0
             grind)
          | exact superpose b2e953 b2e2152
          | exact resolve b2e2152 b2e953
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e953 b2e2152
        have b2e3825 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e2208 (σ y)
             have i₂ := b2e943
             grind)
          | exact superpose b2e943 b2e2208
          | exact resolve b2e2208 b2e943
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e943 b2e2208
        have b2e4136 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e3825
             grind)
          | exact superpose b2e3825 b2e22
          | exact resolve b2e22 b2e3825
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3825
        have b2e15467 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1945
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e1945
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e1945 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1945
        have b2e15468 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15467
        have b2e15469 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15468
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15468
          | exact resolve b2e15468 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15468
        have b2e15470 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15469
        have b2e15476 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e15470
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15470
          | exact resolve b2e15470 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15470
        have b2e15487 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e908 x
             have i₂ := b2e15476
             grind)
          | exact superpose b2e15476 b2e908
          | exact resolve b2e908 b2e15476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e908 b2e15476
        have b2e15534 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e15487
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e15487
          | exact resolve b2e15487 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15487
        have b2e16395 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e15534
             grind)
          | exact superpose b2e15534 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e15534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15534
        have b2e16396 : x = (M.op x x) ∨ x = y := by grind
        clear b2e16395
        have b2e16405 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e16396
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16396
          | exact resolve b2e16396 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16396
        have b2e16406 : x = y := by grind
        clear b2e16405
        have b2e17518 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e4136
             have i₂ := b2e16406
             grind)
          | exact superpose b2e16406 b2e4136
          | exact resolve b2e4136 b2e16406
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4136 b2e16406
        have b2e17519 : False := by grind
        exact b2e17519
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e47 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
          first
          | (have i₁ := b3e47 (M.op x x)
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e47
          | exact resolve b3e47 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x X1
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e12
          | exact resolve b3e12 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 (M.op x X0) X0
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e12
          | exact resolve b3e12 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b3e48
             have i₂ := b3e50 (M.op y x) x
             grind)
          | exact superpose b3e50 b3e48
          | exact resolve b3e48 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e54 : (M.op y (M.op x x)) = (M.op y y) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e53
          | exact resolve b3e53 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e91 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (M.op x x) y
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e12
          | exact resolve b3e12 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e94 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b3e91 X0
             have i₂ := b3e51 x X0
             grind)
          | exact superpose b3e51 b3e91
          | exact resolve b3e91 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e91
        have b3e97 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b3e94 X0
             have i₂ := b3e50 X0 y
             grind)
          | exact superpose b3e50 b3e94
          | exact resolve b3e94 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e94
        have b3e118 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e97 X0
             grind)
          | exact superpose b3e97 b3e12
          | exact resolve b3e12 b3e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97
        have b3e192 : y = (M.op x y) := by
          first
          | (have i₁ := b3e118 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e118
          | exact resolve b3e118 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e118
        have b3e2371 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e78 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e78
          | exact resolve b3e78 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e2485 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e2371
        have b3e3328 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e2485
             grind)
          | exact superpose b3e2485 b3e13
          | exact resolve b3e13 b3e2485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2485
        have b3e3344 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e3328
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e3328
          | exact resolve b3e3328 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3328
        have b3e3352 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e3344
             grind)
          | exact superpose b3e3344 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e3344
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3344
        have b3e3353 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e3352
        have b3e3355 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e3353
             have r₂ := b3e20
             grind)
          | exact resolve b3e3353 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3353
        have b3e3553 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e47 x
             have i₂ := b3e3355
             grind)
          | exact superpose b3e3355 b3e47
          | exact resolve b3e47 b3e3355
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e3355
        have b3e3572 : y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e3553
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3553
          | exact resolve b3e3553 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3553
        have b3e3574 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e3572
             have r₂ := b3e20
             grind)
          | exact resolve b3e3572 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3572
        have b3e3734 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e3574
             grind)
          | exact superpose b3e3574 b3e19
          | exact resolve b3e19 b3e3574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3759 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e3734
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e3734
          | exact resolve b3e3734 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3734
        have b3e3764 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e3759
             have i₂ := b3e3574
             grind)
          | exact superpose b3e3574 b3e3759
          | exact resolve b3e3759 b3e3574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3759
        have b3e3769 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e3764
             have i₂ := b3e192
             grind)
          | exact superpose b3e192 b3e3764
          | exact resolve b3e3764 b3e192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e192 b3e3764
        have b3e3770 : False := by grind
        exact b3e3770
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X1 X3
               have i₂ := b4e13 X2 X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X1 X2) X2
               have i₂ := b4e13 X2 X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 X0 (M.op x X1)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
            first
            | (have i₁ := b4e35 (M.op x x)
               have i₂ := b4e35 x
               grind)
            | exact superpose b4e35 b4e35
            | exact resolve b4e35 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op x X0) X0
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e41 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b4e36
               have i₂ := b4e38 (M.op y x) x
               grind)
            | exact superpose b4e38 b4e36
            | exact resolve b4e36 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e42 : (M.op y (M.op x x)) = (M.op y y) := by
            first
            | (have i₁ := b4e41
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e41
            | exact resolve b4e41 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e87 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (M.op x x) y
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e13
            | exact resolve b4e13 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e90 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b4e87 X0
               have i₂ := b4e39 x X0
               grind)
            | exact superpose b4e39 b4e87
            | exact resolve b4e87 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e87
          have b4e93 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b4e90 X0
               have i₂ := b4e38 X0 y
               grind)
            | exact superpose b4e38 b4e90
            | exact resolve b4e90 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e90
          have b4e114 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e93 X0
               grind)
            | exact superpose b4e93 b4e13
            | exact resolve b4e13 b4e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e151 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X0 (σ x) X1 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e31
            | exact resolve b4e31 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e188 : y = (M.op x y) := by
            first
            | (have i₁ := b4e114 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e114
            | exact resolve b4e114 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114
          have b4e374 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (M.op X2 X1) X1
               have i₂ := b4e33 X1 X2 X0
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e655 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 (σ y) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e771 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 (M.op (M.op x X0) X1)
               have i₂ := b4e32 x X0 X1 (σ y)
               grind)
            | exact superpose b4e32 b4e30
            | exact resolve b4e30 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e32
          have b4e774 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b4e771 X0 X1
               have i₂ := b4e13 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
               grind)
            | exact superpose b4e13 b4e771
            | exact resolve b4e771 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e771
          have b4e819 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e655 X0 x
               have i₂ := b4e151 (M.op x (σ y)) X0
               grind)
            | exact superpose b4e151 b4e655
            | exact resolve b4e655 b4e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e151 b4e655
          have b4e825 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b4e774 x x
               have i₂ := b4e374 (σ x) (σ y) (M.op x x)
               grind)
            | exact superpose b4e374 b4e774
            | exact resolve b4e774 b4e374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e374 b4e774
          have b4e843 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e825
               have i₂ := b4e819 (σ x)
               grind)
            | exact superpose b4e819 b4e825
            | exact resolve b4e825 b4e819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e819 b4e825
          have b4e849 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e843
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e843
            | exact resolve b4e843 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e843
          have b4e850 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e849
               grind)
            | exact superpose b4e849 b4e20
            | exact resolve b4e20 b4e849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e849
          have b4e864 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e850
               have i₂ := b4e188
               grind)
            | exact superpose b4e188 b4e850
            | exact resolve b4e850 b4e188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188 b4e850
          have b4e865 : False := by grind
          exact b4e865
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op X2 X1) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X1 X3
               have i₂ := b5e13 X2 X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X1 X2) X2
               have i₂ := b5e13 X2 X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X0 (M.op x X1)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 x X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e45 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e41
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
          have b5e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e54 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X2 X1)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e70 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op y (M.op x (M.op X0 x))) := by
            intro X0
            first
            | (have i₁ := b5e31 (M.op X0 x)
               have i₂ := b5e36 (M.op x (M.op X0 x)) X0
               grind)
            | exact superpose b5e36 b5e31
            | exact resolve b5e31 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e78 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e96 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e27 X1 X0
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e143 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X3) = (M.op (M.op X2 X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e30 X2 X0 X3 (M.op x X1)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e30
            | exact resolve b5e30 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e173 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) = (M.op (M.op X4 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 (M.op X3 X1) X2 X4
               have i₂ := b5e30 X3 X1 (M.op X2 (M.op X3 X1)) X0
               grind)
            | (have i₁ := b5e13 (M.op X3 X1) X2 X4
               have i₂ := b5e30 X0 X1 (M.op X2 (M.op X3 X1)) X3
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e263 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X3 (M.op X2 X1)) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e30 X1 (M.op X2 X1) X0 X3
               have i₂ := b5e33 X1 X2 X0
               grind)
            | exact superpose b5e33 b5e30
            | exact resolve b5e30 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e264 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 (M.op X2 X1) X1
               have i₂ := b5e33 X1 X2 X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e350 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 x X0
               have i₂ := b5e29 X0 X1 x X1
               grind)
            | exact superpose b5e29 b5e33
            | exact resolve b5e33 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e958 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e959 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e958
               have r₂ := b5e24
               grind)
            | exact resolve b5e958 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e958
          have b5e960 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e959
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e959
            | exact resolve b5e959 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e959
          have b5e961 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e960
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e960
            | exact resolve b5e960 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e960
          have b5e964 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ y) (σ x)
               have i₂ := b5e961
               grind)
            | exact superpose b5e961 b5e13
            | exact resolve b5e13 b5e961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e969 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (σ y) X1))) = (M.op (M.op X0 (σ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X1 (σ y) (σ x) X0
               have i₂ := b5e961
               grind)
            | exact superpose b5e961 b5e29
            | exact resolve b5e29 b5e961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e971 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 X0 (σ y) X1 (σ x)
               have i₂ := b5e961
               grind)
            | exact superpose b5e961 b5e30
            | exact resolve b5e30 b5e961
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e961
          have b5e976 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X1)) = (M.op (M.op X0 (σ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e969 X0 X1
               have i₂ := b5e350 X1 (σ y)
               grind)
            | exact superpose b5e350 b5e969
            | exact resolve b5e969 b5e350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e350 b5e969
          have b5e981 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e976 X0 X1
               have i₂ := b5e964 X1
               grind)
            | exact superpose b5e964 b5e976
            | exact resolve b5e976 b5e964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e964 b5e976
          have b5e1102 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e54 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e1829 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e50 X1 X0
               grind)
            | exact superpose b5e50 b5e17
            | (have j0 := b5e17 (σ X1) (σ X0)
               have j1 := b5e50 X1 X0
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e50 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e50 X0 X1
               grind)
            | exact resolve b5e17 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e1852 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e1829 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1829
          have b5e1853 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e1852 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1852
          have b5e1868 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1853 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e1853
            | (have j0 := b5e1853 X0 X1
               grind)
            | exact resolve b5e1853 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1853
          have b5e2383 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (M.op X2 X1) (σ y)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e32 X2 X1 (σ y) X0
               have i₂ := b5e971 X1 X0
               grind)
            | exact superpose b5e971 b5e32
            | exact resolve b5e32 b5e971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e2412 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e2383 X0 x x
               have i₂ := b5e971 (M.op x x) X0
               grind)
            | exact superpose b5e971 b5e2383
            | exact resolve b5e2383 b5e971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e971 b5e2383
          have b5e2846 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 (M.op X4 X1)) X2) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e30 X3 (M.op X4 X1) X2 X1
               have i₂ := b5e143 X1 X4 X0 X2
               grind)
            | exact superpose b5e143 b5e30
            | exact resolve b5e30 b5e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143
          have b5e3159 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op X3 (M.op X4 X2)) (M.op X1 X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e263 (M.op X1 X2) X2 X4 X3
               have i₂ := b5e13 X2 X1 X0
               grind)
            | exact superpose b5e13 b5e263
            | exact resolve b5e263 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e263
          have b5e11854 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) = X4 ∨ (M.op (M.op X3 X2) X4) = (k (M.op X3 X2) X4) ∨ (M.op X4 (M.op X3 X2)) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e18 (M.op X3 X2) X4
               have i₂ := b5e2846 X3 X2 (M.op X3 X2) X0 X1
               grind)
            | exact superpose b5e2846 b5e18
            | (have j0 := b5e18 (M.op X3 X2) X4
               grind)
            | exact resolve b5e18 b5e2846
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2846
          have b5e61228 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1102 X0 (σ x)
               have i₂ := b5e2412 (σ x)
               grind)
            | exact superpose b5e2412 b5e1102
            | (have j0 := b5e1102 X0 (σ x)
               grind)
            | (have r₁ := b5e1102 (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ x)))) (σ x)
               have r₂ := b5e2412 (M.op (σ x) (σ x))
               grind)
            | (have r₁ := b5e1102 (M.op (σ x) (σ x)) (σ x)
               have r₂ := b5e2412 (σ x)
               grind)
            | exact resolve b5e1102 b5e2412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2412
          have b5e61233 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) ≠ X3 ∨ (M.op (M.op X1 X2) X3) = (k (M.op X1 X2) X3) ∨ (M.op X3 (M.op X1 X2)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e1102 X3 (M.op X1 X2)
               have i₂ := b5e173 X1 X2 (M.op X1 X2) X1 X0
               grind)
            | exact superpose b5e173 b5e1102
            | (have j0 := b5e1102 X3 (M.op X1 X2)
               grind)
            | (have r₁ := b5e1102 (M.op (M.op x (M.op X3 X1)) (M.op X3 X1)) (M.op X3 X1)
               have r₂ := b5e173 X3 X1 (M.op X3 X1) X3 x
               grind)
            | (have r₁ := b5e1102 (M.op (M.op X0 (M.op x X2)) (M.op X2 (M.op (M.op x X2) (M.op x X2)))) (M.op x X2)
               have r₂ := b5e173 X0 (M.op x X2) X2 (M.op x X2) x
               grind)
            | exact resolve b5e1102 b5e173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e173 b5e1102
          have b5e61315 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (k (M.op X1 X2) X3) ∨ (M.op X3 (M.op X1 X2)) = X3 := by
            intro X1 X2 X3
            first
            | (have j0 := b5e61233 x X1 X2 X3
               have j1 := b5e11854 x X1 X2 X1 X3
               grind)
            | (have r₁ := b5e61233 x X3 X2 x
               have r₂ := b5e11854 x X3 X2 X3 x
               grind)
            | (have r₁ := b5e61233 x X1 X2 (M.op (M.op x (M.op X1 X2)) (M.op X3 X2))
               have r₂ := b5e11854 x X1 X2 X3 (M.op (M.op x (M.op X1 X2)) (M.op X1 X2))
               grind)
            | (have r₁ := b5e61233 X3 X1 X2 (k (M.op X3 (M.op X1 X2)) (M.op X1 X2))
               have r₂ := b5e11854 x X1 (M.op X1 X2) X3 (M.op X1 X2)
               grind)
            | exact resolve b5e61233 b5e11854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11854 b5e61233
          have b5e61319 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b5e61228 X0
               have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e61228 (k (σ x) (σ x))
               have r₂ := b5e18 (σ x) (σ x)
               grind)
            | (have r₁ := b5e61228 x
               have r₂ := b5e18 (σ x) x
               grind)
            | (have r₁ := b5e61228 (M.op X0 X0)
               have r₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact resolve b5e61228 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61228
          have b5e167070 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e19 x X0
               have i₂ := b5e61319 (σ X0)
               grind)
            | exact superpose b5e61319 b5e19
            | (have j1 := b5e61319 (σ X0)
               grind)
            | exact resolve b5e19 b5e61319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61319
          have b5e204934 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e1868
          have b5e205133 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e204934 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e204934
            | (have j0 := b5e204934 X0 X1
               grind)
            | exact resolve b5e204934 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e204934
          have b5e205134 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e205133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e205133
          have b5e242483 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e205134 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e205134
            | exact resolve b5e205134 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e205134
          have b5e242678 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e242483 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e242483
            | (have j0 := b5e242483 X0 X1
               grind)
            | exact resolve b5e242483 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242483
          have b5e242688 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e242678 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e242678
            | (have j0 := b5e242678 X0 X1
               grind)
            | exact resolve b5e242678 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242678
          have b5e255420 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e242688 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e242688
            | exact resolve b5e242688 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242688
          have b5e256300 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e255420 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e259388 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (k (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e256300 (M.op X3 X1) X2
               have i₂ := b5e30 X3 X1 X2 X0
               grind)
            | (have i₁ := b5e256300 (M.op X3 X1) X2
               have i₂ := b5e30 X0 X1 X2 X3
               grind)
            | exact superpose b5e30 b5e256300
            | (have j0 := b5e256300 (M.op X3 X1) X2
               grind)
            | (have r₁ := b5e256300 (M.op (M.op X3 X2) X2) X2
               have r₂ := b5e30 (M.op X3 X2) X2 X2 X3
               grind)
            | (have r₁ := b5e256300 (M.op (M.op X0 X2) X2) X2
               have r₂ := b5e30 X0 X2 X2 (M.op X0 X2)
               grind)
            | exact resolve b5e256300 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e660514 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e256300 (σ X0) (σ x)
               have i₂ := b5e167070 X0
               grind)
            | exact superpose b5e167070 b5e256300
            | (have j0 := b5e256300 (σ X0) (σ x)
               have j1 := b5e167070 X0
               grind)
            | (have r₁ := b5e256300 (σ X0) (σ x)
               have r₂ := b5e167070 X0
               grind)
            | exact resolve b5e256300 b5e167070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167070
          have b5e660516 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e660514 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e660514
          have b5e660519 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e660516 X0
               have i₂ := b5e19 X0 x
               grind)
            | exact superpose b5e19 b5e660516
            | (have j0 := b5e660516 X0
               grind)
            | exact resolve b5e660516 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e660516
          have b5e665227 : ∀ X0 : G, (M.op (σ x) X0) = (σ (k x (τ X0))) ∨ (σ (k (τ X0) x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e660519 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e660519
            | exact resolve b5e660519 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e660519
          have b5e665275 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ (k (τ X0) x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e665227 X0
               have i₂ := b5e27 X0 x
               grind)
            | exact superpose b5e27 b5e665227
            | (have j0 := b5e665227 X0
               grind)
            | exact resolve b5e665227 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e665227
          have b5e665277 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e665275 X0
               have i₂ := b5e26 X0 x
               grind)
            | exact superpose b5e26 b5e665275
            | (have j0 := b5e665275 X0
               grind)
            | exact resolve b5e665275 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e665275
          have b5e671923 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e96 X0 (σ x)
               have i₂ := b5e665277 (σ X0)
               grind)
            | exact superpose b5e665277 b5e96
            | (have j1 := b5e665277 (σ X0)
               grind)
            | exact resolve b5e96 b5e665277
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96 b5e665277
          have b5e671938 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e671923 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e671923
            | (have j0 := b5e671923 X0
               grind)
            | exact resolve b5e671923 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e671923
          have b5e671944 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op (σ x) (σ X0)) = (k (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e671938 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e671938
            | (have j0 := b5e671938 X0
               grind)
            | exact resolve b5e671938 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e671938
          have b5e671945 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e671944 X0
               have i₂ := b5e19 x X0
               grind)
            | exact superpose b5e19 b5e671944
            | (have j0 := b5e671944 X0
               grind)
            | exact resolve b5e671944 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e671944
          have b5e822364 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) X1) := by
            intro X0 X1
            first
            | (have j0 := b5e259388 X0 X1 X1 (M.op X0 X1)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e259388
          have b5e824178 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
            first
            | (have i₁ := b5e822364 x (σ x)
               have i₂ := b5e981 x (σ x)
               grind)
            | exact superpose b5e981 b5e822364
            | exact resolve b5e822364 b5e981
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e981 b5e822364
          have b5e836525 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
            first
            | (have i₁ := b5e78 (M.op (σ x) (σ x)) x
               have i₂ := b5e824178
               grind)
            | exact superpose b5e824178 b5e78
            | exact resolve b5e78 b5e824178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78 b5e824178
          have b5e840463 : (τ (σ (k x x))) = (k (τ (σ (k x x))) x) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e836525
               have i₂ := b5e671945 x
               grind)
            | exact superpose b5e671945 b5e836525
            | (have j1 := b5e671945 (τ (σ (k x x)))
               grind)
            | exact resolve b5e836525 b5e671945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e671945 b5e836525
          have b5e840486 : (k x x) = (k (k x x) x) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e840463
               have i₂ := b5e14 (k x x)
               grind)
            | exact superpose b5e14 b5e840463
            | exact resolve b5e840463 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840463
          have b5e840583 : (M.op x x) = (k (M.op x x) x) ∨ x = (M.op x x) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e840486
               have i₂ := b5e255420 x x
               grind)
            | exact superpose b5e255420 b5e840486
            | (have j1 := b5e255420 x (M.op x x)
               grind)
            | exact resolve b5e840486 b5e255420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e255420 b5e840486
          have b5e840584 : (M.op x x) = (k (M.op x x) x) ∨ x = (k x x) := by
            first
            | (have j1 := b5e256300 (M.op x x) x
               grind)
            | (have r₁ := b5e840583
               have r₂ := b5e256300 x x
               grind)
            | exact resolve b5e840583 b5e256300
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e256300 b5e840583
          have b5e840728 : (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x (M.op x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e61315 x x x
               have i₂ := b5e840584
               grind)
            | exact superpose b5e840584 b5e61315
            | (have j0 := b5e61315 x x x
               grind)
            | exact resolve b5e61315 b5e840584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61315 b5e840584
          have b5e840729 : (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x (M.op x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e840728
               have i₂ := b5e13 x x x
               grind)
            | exact superpose b5e13 b5e840728
            | exact resolve b5e840728 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840728
          have b5e840731 : (M.op x x) = (M.op y x) ∨ x = (M.op x (M.op x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e840729
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e840729
            | exact resolve b5e840729 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840729
          have b5e840733 : y = (M.op x x) ∨ x = (M.op x (M.op x x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e840731
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e840731
            | exact resolve b5e840731 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840731
          have b5e840735 : x = (M.op x (M.op x x)) ∨ x = (k x x) := by
            first
            | (have r₁ := b5e840733
               have r₂ := b5e21
               grind)
            | exact resolve b5e840733 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840733
          have b5e840737 : x = (M.op y x) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e840735
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e840735
            | exact resolve b5e840735 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840735
          have b5e840739 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e840737
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e840737
            | exact resolve b5e840737 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840737
          have b5e841508 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e840739
               grind)
            | exact superpose b5e840739 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e840739
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e840739
          have b5e841509 : x = (M.op x x) ∨ x = y := by grind
          clear b5e841508
          have b5e842260 : (M.op x x) = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b5e31 x
               have i₂ := b5e841509
               grind)
            | exact superpose b5e841509 b5e31
            | exact resolve b5e31 b5e841509
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e841509
          have b5e842538 : y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e842260
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e842260
            | exact resolve b5e842260 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e842260
          have b5e842609 : x = y := by
            first
            | (have r₁ := b5e842538
               have r₂ := b5e21
               grind)
            | exact resolve b5e842538 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e842538
          have b5e842844 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 x)) y) = (M.op y (M.op (M.op X0 y) x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e3159 X0 y x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3159
            | exact resolve b5e3159 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3159
          have b5e843125 : ∀ X1 X2 : G, (M.op y (M.op x (M.op y x))) = (M.op (M.op X1 (M.op X2 x)) y) := by
            intro X1 X2
            first
            | (have i₁ := b5e842844 x X1 X2
               have i₂ := b5e13 x y x
               grind)
            | exact superpose b5e13 b5e842844
            | exact resolve b5e842844 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e842844
          have b5e843197 : ∀ X2 : G, (M.op y (M.op x (M.op y x))) = (M.op y (M.op (M.op X2 x) y)) := by
            intro X2
            first
            | (have i₁ := b5e843125 x X2
               have i₂ := b5e13 y (M.op X2 x) x
               grind)
            | exact superpose b5e13 b5e843125
            | exact resolve b5e843125 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e843125
          have b5e843240 : (M.op y (M.op x y)) = (M.op y (M.op x (M.op y x))) := by
            first
            | (have i₁ := b5e843197 x
               have i₂ := b5e264 y x x
               grind)
            | exact superpose b5e264 b5e843197
            | exact resolve b5e843197 b5e264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e264 b5e843197
          have b5e843271 : (M.op y (M.op y x)) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b5e843240
               have i₂ := b5e70 y
               grind)
            | exact superpose b5e70 b5e843240
            | exact resolve b5e843240 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e843240
          have b5e843295 : (M.op y (M.op y x)) = (M.op y y) := by
            first
            | (have i₁ := b5e843271
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e843271
            | exact resolve b5e843271 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e843271
          have b5e843307 : (M.op x x) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e843295
               have i₂ := b5e842609
               grind)
            | exact superpose b5e842609 b5e843295
            | exact resolve b5e843295 b5e842609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e842609 b5e843295
          have b5e843312 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b5e843307
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e843307
            | exact resolve b5e843307 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e843307
          have b5e843316 : y = (M.op x x) := by
            first
            | (have i₁ := b5e843312
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e843312
            | exact resolve b5e843312 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e843312
          have b5e843319 : False := by grind
          exact b5e843319
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e46 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 X0 (M.op x X1)
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e76 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e84 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e76
             have r₂ := b6e20
             grind)
          | exact resolve b6e76 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e87 : x = (M.op x y) := by
          first
          | (have r₁ := b6e84
             have r₂ := b6e21
             grind)
          | exact resolve b6e84 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e90 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 y x
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e12
          | exact resolve b6e12 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e257 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b6e46 y x X0
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e46
          | exact resolve b6e46 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e291 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b6e257 X0
             have i₂ := b6e90 X0
             grind)
          | exact superpose b6e90 b6e257
          | exact resolve b6e257 b6e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90 b6e257
        have b6e319 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e291 X0
             grind)
          | exact superpose b6e291 b6e12
          | exact resolve b6e12 b6e291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e291
        have b6e1034 : x = (M.op y x) := by
          first
          | (have i₁ := b6e319 y
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e319
          | exact resolve b6e319 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87 b6e319
        have b6e1101 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e1034
             grind)
          | exact superpose b6e1034 b6e21
          | exact resolve b6e21 b6e1034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1034
        have b6e1894 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e74 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e74
          | exact resolve b6e74 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e1997 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1894
        have b6e2951 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1997
             grind)
          | exact superpose b6e1997 b6e13
          | exact resolve b6e13 b6e1997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2967 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2951
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2951
          | exact resolve b6e2951 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2951
        have b6e2975 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e2967
             grind)
          | exact superpose b6e2967 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e2967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2967
        have b6e2976 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2975
        have b6e2978 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2976
             have r₂ := b6e20
             grind)
          | exact resolve b6e2976 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2976
        have b6e3292 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2978
        have b6e3654 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1997
             have i₂ := b6e3292
             grind)
          | exact superpose b6e3292 b6e1997
          | exact resolve b6e1997 b6e3292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1997 b6e3292
        have b6e3661 : (σ x) = (σ y) := by grind
        clear b6e3654
        have b6e3940 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3661
             grind)
          | exact superpose b6e3661 b6e13
          | exact resolve b6e13 b6e3661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3661
        have b6e3959 : x = y := by
          first
          | (have i₁ := b6e3940
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3940
          | exact resolve b6e3940 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3940
        have b6e3965 : False := by grind
        exact b6e3965
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
          have b7e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e28 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X1 X3
               have i₂ := b7e13 X2 X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X1 X2) X2
               have i₂ := b7e13 X2 X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X0 (M.op x X1)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k (τ X0) X1)
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e14
            | exact resolve b7e14 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e45 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ x) = (σ (k x y)) := by
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
          have b7e49 : (k x y) = (τ (σ x)) := by
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
          have b7e50 : x = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 X2
               have i₂ := b7e18 X2 X0
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X2 X1)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X2 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e67 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e21
               grind)
            | exact resolve b7e66 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e69 : x = (M.op x y) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e77 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b7e81 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e13
            | exact resolve b7e13 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e99 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X3) = (M.op (M.op X2 X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e31 X2 X0 X3 (M.op x X1)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e100 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 X0 (σ x) X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e31
            | exact resolve b7e31 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e120 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) = (M.op (M.op X4 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 (M.op X3 X1) X2 X4
               have i₂ := b7e31 X3 X1 (M.op X2 (M.op X3 X1)) X0
               grind)
            | (have i₁ := b7e13 (M.op X3 X1) X2 X4
               have i₂ := b7e31 X0 X1 (M.op X2 (M.op X3 X1)) X3
               grind)
            | exact superpose b7e31 b7e13
            | exact resolve b7e13 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e135 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ x) X0)) X1) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e31 X0 (M.op (σ x) X0) X1 X2
               have i₂ := b7e32 X0
               grind)
            | exact superpose b7e32 b7e31
            | exact resolve b7e31 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e235 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
            intro X0
            first
            | (have i₁ := b7e34 (σ x) (M.op x (σ y)) X0
               have i₂ := b7e28 x
               grind)
            | exact superpose b7e28 b7e34
            | exact resolve b7e34 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e238 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op y x) X0) := by
            intro X0
            first
            | (have i₁ := b7e34 y x X0
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e34
            | exact resolve b7e34 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e267 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 (M.op X2 X1) X1
               have i₂ := b7e34 X1 X2 X0
               grind)
            | exact superpose b7e34 b7e13
            | exact resolve b7e13 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e272 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y x) X0) := by
            intro X0
            first
            | (have i₁ := b7e238 X0
               have i₂ := b7e81 X0
               grind)
            | exact superpose b7e81 b7e238
            | exact resolve b7e238 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e238
          have b7e274 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (σ y) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e235 X0
               have i₂ := b7e135 (σ y) X0 (σ x)
               grind)
            | exact superpose b7e135 b7e235
            | exact resolve b7e235 b7e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135 b7e235
          have b7e279 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e274 X0
               have i₂ := b7e32 X0
               grind)
            | exact superpose b7e32 b7e274
            | exact resolve b7e274 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e274
          have b7e299 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e272 X0
               grind)
            | exact superpose b7e272 b7e13
            | exact resolve b7e13 b7e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e272
          have b7e534 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X1 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e638 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e28 (M.op (M.op x X0) X1)
               have i₂ := b7e33 x X0 X1 (σ y)
               grind)
            | exact superpose b7e33 b7e28
            | exact resolve b7e28 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e640 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e638 X0 X1
               have i₂ := b7e13 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
               grind)
            | exact superpose b7e13 b7e638
            | exact resolve b7e638 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e638
          have b7e680 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e534 X0 x
               have i₂ := b7e100 (M.op x (σ y)) X0
               grind)
            | exact superpose b7e100 b7e534
            | exact resolve b7e534 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100 b7e534
          have b7e686 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b7e640 x x
               have i₂ := b7e267 (σ x) (σ y) (M.op x x)
               grind)
            | exact superpose b7e267 b7e640
            | exact resolve b7e640 b7e267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e267 b7e640
          have b7e701 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e686
               have i₂ := b7e680 (σ x)
               grind)
            | exact superpose b7e680 b7e686
            | exact resolve b7e686 b7e680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e686
          have b7e706 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e701
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e701
            | exact resolve b7e701 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e701
          have b7e1038 : x = (M.op y x) := by
            first
            | (have i₁ := b7e299 y
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e299
            | exact resolve b7e299 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e299
          have b7e1216 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e60 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e1276 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e1038
               grind)
            | exact superpose b7e1038 b7e22
            | exact resolve b7e22 b7e1038
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1038
          have b7e1878 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X1) (σ X0)
               have i₂ := b7e55 X1 X0
               grind)
            | exact superpose b7e55 b7e17
            | (have j0 := b7e17 (σ X1) (σ X0)
               have j1 := b7e55 X1 X0
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X1)
               have r₂ := b7e55 X1 X1
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e55 X0 X1
               grind)
            | exact resolve b7e17 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e1901 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e1878 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1878
          have b7e1902 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e1901 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1901
          have b7e1915 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e1902 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e1902
            | (have j0 := b7e1902 X0 X1
               grind)
            | exact resolve b7e1902 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1902
          have b7e3069 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 (M.op X4 X1)) X2) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e31 X3 (M.op X4 X1) X2 X1
               have i₂ := b7e99 X1 X4 X0 X2
               grind)
            | exact superpose b7e99 b7e31
            | exact resolve b7e31 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e6025 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) = X4 ∨ (M.op (M.op X3 X2) X4) = (k (M.op X3 X2) X4) ∨ (M.op X4 (M.op X3 X2)) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e18 (M.op X3 X2) X4
               have i₂ := b7e3069 X3 X2 (M.op X3 X2) X0 X1
               grind)
            | exact superpose b7e3069 b7e18
            | (have j0 := b7e18 (M.op X3 X2) X4
               grind)
            | exact resolve b7e18 b7e3069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3069
          have b7e60321 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1216 X0 (σ y)
               have i₂ := b7e680 (σ y)
               grind)
            | exact superpose b7e680 b7e1216
            | (have j0 := b7e1216 X0 (σ y)
               grind)
            | (have r₁ := b7e1216 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) (σ y)
               have r₂ := b7e680 (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b7e1216 (M.op (σ y) (σ y)) (σ y)
               have r₂ := b7e680 (σ y)
               grind)
            | exact resolve b7e1216 b7e680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e680
          have b7e60325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) ≠ X3 ∨ (M.op (M.op X1 X2) X3) = (k (M.op X1 X2) X3) ∨ (M.op X3 (M.op X1 X2)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e1216 X3 (M.op X1 X2)
               have i₂ := b7e120 X1 X2 (M.op X1 X2) X1 X0
               grind)
            | exact superpose b7e120 b7e1216
            | (have j0 := b7e1216 X3 (M.op X1 X2)
               grind)
            | (have r₁ := b7e1216 (M.op (M.op x (M.op X3 X1)) (M.op X3 X1)) (M.op X3 X1)
               have r₂ := b7e120 X3 X1 (M.op X3 X1) X3 x
               grind)
            | (have r₁ := b7e1216 (M.op (M.op X0 (M.op x X2)) (M.op X2 (M.op (M.op x X2) (M.op x X2)))) (M.op x X2)
               have r₂ := b7e120 X0 (M.op x X2) X2 (M.op x X2) x
               grind)
            | exact resolve b7e1216 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120 b7e1216
          have b7e60410 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (k (M.op X1 X2) X3) ∨ (M.op X3 (M.op X1 X2)) = X3 := by
            intro X1 X2 X3
            first
            | (have j0 := b7e60325 x X1 X2 X3
               have j1 := b7e6025 x X1 X2 X1 X3
               grind)
            | (have r₁ := b7e60325 x X3 X2 x
               have r₂ := b7e6025 x X3 X2 X3 x
               grind)
            | (have r₁ := b7e60325 x X1 X2 (M.op (M.op x (M.op X1 X2)) (M.op X3 X2))
               have r₂ := b7e6025 x X1 X2 X3 (M.op (M.op x (M.op X1 X2)) (M.op X1 X2))
               grind)
            | (have r₁ := b7e60325 X3 X1 X2 (k (M.op X3 (M.op X1 X2)) (M.op X1 X2))
               have r₂ := b7e6025 x X1 (M.op X1 X2) X3 (M.op X1 X2)
               grind)
            | exact resolve b7e60325 b7e6025
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6025 b7e60325
          have b7e60414 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b7e60321 X0
               have j1 := b7e18 (σ y) X0
               grind)
            | (have r₁ := b7e60321 (k (σ y) (σ y))
               have r₂ := b7e18 (σ y) (σ y)
               grind)
            | (have r₁ := b7e60321 x
               have r₂ := b7e18 (σ y) x
               grind)
            | (have r₁ := b7e60321 (M.op X0 X0)
               have r₂ := b7e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact resolve b7e60321 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60321
          have b7e61752 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e60414 (σ X0)
               grind)
            | exact superpose b7e60414 b7e19
            | (have j1 := b7e60414 (σ X0)
               grind)
            | exact resolve b7e19 b7e60414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60414
          have b7e233474 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b7e1915
          have b7e233683 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e233474 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e233474
            | (have j0 := b7e233474 X0 X1
               grind)
            | exact resolve b7e233474 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e233474
          have b7e233684 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e233683 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e233683
          have b7e233742 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e233684 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e233684
            | exact resolve b7e233684 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e233999 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e233742 X0 X1
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e233742
            | (have j0 := b7e233742 X0 X1
               grind)
            | exact resolve b7e233742 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e233742
          have b7e234015 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e233999 X0 X1
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e233999
            | (have j0 := b7e233999 X0 X1
               grind)
            | exact resolve b7e233999 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e233999
          have b7e240019 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e234015 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e234015
            | exact resolve b7e234015 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e234015
          have b7e240665 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e27 X1 X0
               have i₂ := b7e240019 (τ X1) X0
               grind)
            | exact superpose b7e240019 b7e27
            | (have j1 := b7e240019 (τ X1) X0
               grind)
            | exact resolve b7e27 b7e240019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e240741 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e240019 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e242415 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (k (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e240741 (M.op X3 X1) X2
               have i₂ := b7e31 X3 X1 X2 X0
               grind)
            | (have i₁ := b7e240741 (M.op X3 X1) X2
               have i₂ := b7e31 X0 X1 X2 X3
               grind)
            | exact superpose b7e31 b7e240741
            | (have j0 := b7e240741 (M.op X3 X1) X2
               grind)
            | (have r₁ := b7e240741 (M.op (M.op X3 X2) X2) X2
               have r₂ := b7e31 (M.op X3 X2) X2 X2 X3
               grind)
            | (have r₁ := b7e240741 (M.op (M.op X0 X2) X2) X2
               have r₂ := b7e31 X0 X2 X2 (M.op X0 X2)
               grind)
            | exact resolve b7e240741 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e278175 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e240665 X0 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e240665
            | exact resolve b7e240665 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e240665
          have b7e278236 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e278175 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e278175
            | (have j0 := b7e278175 X0 X1
               grind)
            | exact resolve b7e278175 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e278175
          have b7e529853 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) ∨ (σ X0) = (σ (k X0 y)) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b7e233684 y X0
               have i₂ := b7e61752 X0
               grind)
            | exact superpose b7e61752 b7e233684
            | (have j0 := b7e233684 X0 y
               have j1 := b7e61752 X0
               grind)
            | exact resolve b7e233684 b7e61752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61752 b7e233684
          have b7e529894 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have j0 := b7e529853 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e529853
          have b7e533024 : ∀ X0 : G, (M.op (σ y) X0) = (σ (k y (τ X0))) ∨ (σ (k (τ X0) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e529894 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e529894
            | exact resolve b7e529894 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e529894
          have b7e533098 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ (k (τ X0) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e533024 X0
               have i₂ := b7e27 X0 y
               grind)
            | exact superpose b7e27 b7e533024
            | (have j0 := b7e533024 X0
               grind)
            | exact resolve b7e533024 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27 b7e533024
          have b7e533103 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e533098 X0
               have i₂ := b7e26 X0 y
               grind)
            | exact superpose b7e26 b7e533098
            | (have j0 := b7e533098 X0
               grind)
            | exact resolve b7e533098 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e533098
          have b7e534894 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e77 X0 (σ y)
               have i₂ := b7e533103 (σ X0)
               grind)
            | exact superpose b7e533103 b7e77
            | (have j1 := b7e533103 (σ X0)
               grind)
            | exact resolve b7e77 b7e533103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e533103
          have b7e534912 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e534894 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e534894
            | (have j0 := b7e534894 X0
               grind)
            | exact resolve b7e534894 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e534894
          have b7e534918 : ∀ X0 : G, (k X0 y) = X0 ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e534912 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e534912
            | (have j0 := b7e534912 X0
               grind)
            | exact resolve b7e534912 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e534912
          have b7e534919 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e534918 X0
               have i₂ := b7e19 y X0
               grind)
            | exact superpose b7e19 b7e534918
            | (have j0 := b7e534918 X0
               grind)
            | exact resolve b7e534918 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e534918
          have b7e535290 : (M.op (σ x) (σ y)) = (M.op (σ (k y y)) (σ x)) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e28 (σ y)
               have i₂ := b7e534919 y
               grind)
            | exact superpose b7e534919 b7e28
            | (have j1 := b7e534919 y
               grind)
            | exact resolve b7e28 b7e534919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e535387 : (σ y) = (M.op (σ (k y y)) (σ x)) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e535290
               have i₂ := b7e706
               grind)
            | exact superpose b7e706 b7e535290
            | exact resolve b7e535290 b7e706
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e706 b7e535290
          have b7e536532 : (σ y) = (M.op (σ (M.op y y)) (σ x)) ∨ y = (k y y) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e535387
               have i₂ := b7e278236 y y
               grind)
            | exact superpose b7e278236 b7e535387
            | (have j1 := b7e278236 y y
               grind)
            | exact resolve b7e535387 b7e278236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e278236 b7e535387
          have b7e536662 : (σ y) = (M.op (σ (M.op y y)) (σ x)) ∨ y = (k y y) := by grind
          clear b7e536532
          have b7e746738 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) X1) := by
            intro X0 X1
            first
            | (have j0 := b7e242415 X0 X1 X1 (M.op X0 X1)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e242415
          have b7e751340 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
            first
            | (have i₁ := b7e746738 (σ y) (σ y)
               have i₂ := b7e279 (σ y)
               grind)
            | exact superpose b7e279 b7e746738
            | exact resolve b7e746738 b7e279
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e279 b7e746738
          have b7e754696 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
            first
            | (have i₁ := b7e39 (M.op (σ y) (σ y)) y
               have i₂ := b7e751340
               grind)
            | exact superpose b7e751340 b7e39
            | exact resolve b7e39 b7e751340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e751340
          have b7e772357 : (τ (σ (k y y))) = (k (τ (σ (k y y))) y) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e754696
               have i₂ := b7e534919 y
               grind)
            | exact superpose b7e534919 b7e754696
            | (have j1 := b7e534919 (τ (σ (k y y)))
               grind)
            | exact resolve b7e754696 b7e534919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e534919 b7e754696
          have b7e772378 : (k y y) = (k (k y y) y) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e772357
               have i₂ := b7e14 (k y y)
               grind)
            | exact superpose b7e14 b7e772357
            | exact resolve b7e772357 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e772357
          have b7e774053 : (M.op y y) = (k (M.op y y) y) ∨ y = (M.op y y) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e772378
               have i₂ := b7e240019 y y
               grind)
            | exact superpose b7e240019 b7e772378
            | (have j1 := b7e240019 y (M.op y y)
               grind)
            | exact resolve b7e772378 b7e240019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e240019 b7e772378
          have b7e774054 : (M.op y y) = (k (M.op y y) y) ∨ y = (k y y) := by
            first
            | (have j1 := b7e240741 (M.op y y) y
               grind)
            | (have r₁ := b7e774053
               have r₂ := b7e240741 y y
               grind)
            | exact resolve b7e774053 b7e240741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e240741 b7e774053
          have b7e774637 : (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y (M.op y y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e60410 y y y
               have i₂ := b7e774054
               grind)
            | exact superpose b7e774054 b7e60410
            | (have j0 := b7e60410 y y y
               grind)
            | exact resolve b7e60410 b7e774054
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60410 b7e774054
          have b7e774638 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y (M.op y y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e774637
               have i₂ := b7e13 y y y
               grind)
            | exact superpose b7e13 b7e774637
            | exact resolve b7e774637 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e774637
          have b7e774640 : (M.op x y) = (M.op y y) ∨ y = (M.op y (M.op y y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e774638
               have i₂ := b7e81 y
               grind)
            | exact superpose b7e81 b7e774638
            | exact resolve b7e774638 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e774638
          have b7e774642 : x = (M.op y y) ∨ y = (M.op y (M.op y y)) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e774640
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e774640
            | exact resolve b7e774640 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e774640
          have b7e774644 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e774642
               have i₂ := b7e81 y
               grind)
            | exact superpose b7e81 b7e774642
            | exact resolve b7e774642 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e774642
          have b7e774646 : x = y ∨ x = (M.op y y) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e774644
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e774644
            | exact resolve b7e774644 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e774644
          have b7e774648 : y = (k y y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e774646
               have r₂ := b7e1276
               grind)
            | exact resolve b7e774646 b7e1276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e774646
          have b7e777959 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e774648
               grind)
            | exact superpose b7e774648 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e774648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e774648
          have b7e777960 : y = (M.op y y) ∨ x = (M.op y y) := by grind
          clear b7e777959
          have b7e781428 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e81 y
               have i₂ := b7e777960
               grind)
            | exact superpose b7e777960 b7e81
            | exact resolve b7e81 b7e777960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e777960
          have b7e781678 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e781428
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e781428
            | exact resolve b7e781428 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e781428
          have b7e781679 : x = (M.op y y) := by grind
          clear b7e781678
          have b7e786094 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) := by
            first
            | (have i₁ := b7e536662
               have i₂ := b7e781679
               grind)
            | exact superpose b7e781679 b7e536662
            | exact resolve b7e536662 b7e781679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e536662
          have b7e786525 : y = (k y y) := by
            first
            | (have r₁ := b7e786094
               have r₂ := b7e23
               grind)
            | exact resolve b7e786094 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e786094
          have b7e791288 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e786525
               grind)
            | exact superpose b7e786525 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e786525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e786525
          have b7e791289 : y = (M.op y y) := by grind
          clear b7e791288
          have b7e791297 : x = y := by
            first
            | (have i₁ := b7e791289
               have i₂ := b7e781679
               grind)
            | exact superpose b7e781679 b7e791289
            | exact resolve b7e791289 b7e781679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e781679 b7e791289
          have b7e791305 : False := by grind
          exact b7e791305
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
          have b8e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e809 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e58 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e810 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e809
               have r₂ := b8e24
               grind)
            | exact resolve b8e809 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e809
          have b8e811 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e810
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e810
            | exact resolve b8e810 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e810
          have b8e812 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e811
               grind)
            | exact superpose b8e811 b8e20
            | exact resolve b8e20 b8e811
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e811
          have b8e981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e812
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e812
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e812 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e812
          have b8e982 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e981
          have b8e984 : y = (M.op y x) := by
            first
            | (have r₁ := b8e982
               have r₂ := b8e21
               grind)
            | exact resolve b8e982 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e982
          have b8e986 : False := by grind
          exact b8e986

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation4478 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4478 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e77 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e82 : False := by grind
      exact b0e82
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : False := by grind
        exact b1e26
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : False := by grind
        exact b2e26
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e34 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (σ y) X1 X2
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X0 y X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x x
               have i₂ := b4e13 X0 X2 x x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e40 x X2
               have i₂ := b4e40 x X0
               grind)
            | (have i₁ := b4e40 X0 x
               have i₂ := b4e40 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e40 b4e40
            | exact resolve b4e40 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e90 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e51 y X0
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e51 X0 y
               grind)
            | exact superpose b4e51 b4e22
            | exact resolve b4e22 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e170 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (σ X0) X2 X3
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e172 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e170 X0 X1 x x
               have i₂ := b4e34 X1 x x
               grind)
            | exact superpose b4e34 b4e170
            | exact resolve b4e170 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e170
          have b4e177 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 (σ y) (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e178 : ∀ X0 X1 : G, (M.op (σ X0) (σ y)) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 (σ X0) (σ X0) X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e34
            | exact resolve b4e34 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e472 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 X1 y
               have i₂ := b4e90 y
               grind)
            | exact superpose b4e90 b4e41
            | exact resolve b4e41 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e90
          have b4e584 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e472 X0 (σ y)
               have i₂ := b4e177 (σ y)
               grind)
            | exact superpose b4e177 b4e472
            | exact resolve b4e472 b4e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177 b4e472
          have b4e750 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e584 (σ x)
               grind)
            | exact superpose b4e584 b4e20
            | exact resolve b4e20 b4e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3591 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ y)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op X0 X0)
               have i₂ := b4e172 X0 (σ (M.op X0 X0))
               grind)
            | exact superpose b4e172 b4e30
            | exact resolve b4e30 b4e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e172
          have b4e3601 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ y)) = (σ (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e3591 X0
               have i₂ := b4e34 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e34 b4e3591
            | exact resolve b4e3591 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e3591
          have b4e3651 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e3601 X0
               have i₂ := b4e584 X0
               grind)
            | exact superpose b4e584 b4e3601
            | exact resolve b4e3601 b4e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3601
          have b4e3685 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e3651 X0
               have i₂ := b4e178 X0 (σ y)
               grind)
            | exact superpose b4e178 b4e3651
            | exact resolve b4e3651 b4e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e178 b4e3651
          have b4e3712 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e3685 X0
               have i₂ := b4e584 (σ X0)
               grind)
            | exact superpose b4e584 b4e3685
            | exact resolve b4e3685 b4e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e584 b4e3685
          have b4e4165 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e750
               have i₂ := b4e3712 x
               grind)
            | exact superpose b4e3712 b4e750
            | (have r₁ := b4e750
               have r₂ := b4e3712 x
               grind)
            | exact resolve b4e750 b4e3712
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e750 b4e3712
          have b4e4177 : False := by grind
          exact b4e4177
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e259 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e269 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e259
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e259
            | exact resolve b5e259 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e259
          have b5e270 : False := by grind
          exact b5e270
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e90 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e118 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e14
            | exact resolve b7e14 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e119 : y = (M.op y y) := by
            first
            | (have i₁ := b7e118
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e118
            | exact resolve b7e118 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e123 : False := by grind
          exact b7e123
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X1) (σ X1)) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e64 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e64
            | (have j0 := b8e64 X0 X1
               grind)
            | exact resolve b8e64 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e80 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e2060 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e74 x y
               grind)
            | exact superpose b8e74 b8e20
            | (have j1 := b8e74 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e2095 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e2060
               have r₂ := b8e80
               grind)
            | exact resolve b8e2060 b8e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80 b8e2060
          have b8e2107 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e2095
               have r₂ := b8e23
               grind)
            | exact resolve b8e2095 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2095
          have b8e2130 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e2107
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2107
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | (have r₁ := b8e2107
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e2107
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e2107 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2107
          have b8e2131 : y = (M.op y y) ∨ x = y := by grind
          clear b8e2130
          have b8e2133 : x = y := by
            first
            | (have r₁ := b8e2131
               have r₂ := b8e22
               grind)
            | exact resolve b8e2131 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2131
          have b8e2136 : False := by grind
          exact b8e2136

/-- `Equation4490`: `x ◇ (y ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4490 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4490 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4490.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X1 X1) X3
           have i₂ := b0e11 (M.op X1 X1) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op X0 (σ y)) := by
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
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X2 X2) X3 X1
           have i₂ := b0e11 X1 X2 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op x X0)
           have i₂ := b0e11 X0 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 (M.op X1 X1)) X1)) := by
        intro X0 X1
        grind
      have b0e43 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e33 x X1 X2 X3
           have i₂ := b0e38 x X1 X1
           grind)
        | exact superpose b0e38 b0e33
        | exact resolve b0e33 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e38
      have b0e45 : (M.op y (σ x)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b0e40 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e40
        | exact resolve b0e40 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e40 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x X0 X1
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0 y
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e11
        | exact resolve b0e11 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e59 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e59
        | exact resolve b0e59 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e74 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X1
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X2 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e92 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e48 X1 (M.op x X0)
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e48
        | exact resolve b0e48 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e108 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e92 X0 X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e92
        | exact resolve b0e92 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92
      have b0e114 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e118 : (M.op (σ x) (σ y)) = (M.op (M.op x (σ y)) (σ x)) := by
        first
        | (have i₁ := b0e34 (σ x) y
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e34
        | exact resolve b0e34 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e127 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e118
           have i₂ := b0e34 (σ y) x
           grind)
        | exact superpose b0e34 b0e118
        | exact resolve b0e118 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e118
      have b0e138 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 x
           have i₂ := b0e60 X0
           grind)
        | exact superpose b0e60 b0e11
        | exact resolve b0e11 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e441 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) x) = (M.op (M.op X0 X0) y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e37 X1 X2 X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37
        | exact resolve b0e37 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e564 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y y)) = (M.op (M.op (M.op X1 X2) X0) x) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e441 X0 X1 X2
           have i₂ := b0e11 X0 y X0
           grind)
        | exact superpose b0e11 b0e441
        | exact resolve b0e441 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e441
      have b0e578 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e564 X0 x x
           have i₂ := b0e11 X0 x (M.op x x)
           grind)
        | exact superpose b0e11 b0e564
        | exact resolve b0e564 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e564
      have b0e580 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e578 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e578
        | exact resolve b0e578 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e578
      have b0e619 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e40 y
           have i₂ := b0e580 x
           grind)
        | exact superpose b0e580 b0e40
        | exact resolve b0e40 b0e580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e658 : ∀ X0 : G, (M.op (M.op y y) y) = (k (M.op (M.op y y) y) (M.op (M.op X0 (M.op (M.op y y) y)) (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b0e42 X0 (M.op y y)
           have i₂ := b0e580 (M.op y y)
           grind)
        | exact superpose b0e580 b0e42
        | exact resolve b0e42 b0e580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e580
      have b0e708 : (M.op (M.op y y) y) = (k (M.op (M.op y y) y) (M.op (M.op (M.op y y) y) (M.op y (M.op y y)))) := by
        first
        | (have i₁ := b0e658 x
           have i₂ := b0e43 y (M.op (M.op y y) y) x
           grind)
        | exact superpose b0e43 b0e658
        | exact resolve b0e658 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e658
      have b0e714 : (M.op (M.op y y) y) = (k (M.op (M.op y y) y) (M.op y (M.op y (M.op y y)))) := by
        first
        | (have i₁ := b0e708
           have i₂ := b0e108 (M.op y y) (M.op y (M.op y y))
           grind)
        | exact superpose b0e108 b0e708
        | exact resolve b0e708 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e708
      have b0e717 : (M.op (M.op y y) y) = (k (M.op (M.op y y) y) (M.op y (M.op y y))) := by
        first
        | (have i₁ := b0e714
           have i₂ := b0e138 y
           grind)
        | exact superpose b0e138 b0e714
        | exact resolve b0e714 b0e138
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e714
      have b0e719 : (M.op (M.op y y) y) = (k (M.op (M.op y y) y) (M.op y y)) := by
        first
        | (have i₁ := b0e717
           have i₂ := b0e138 y
           grind)
        | exact superpose b0e138 b0e717
        | exact resolve b0e717 b0e138
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e717
      have b0e720 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op x y)) := by
        first
        | (have i₁ := b0e719
           have i₂ := b0e619
           grind)
        | exact superpose b0e619 b0e719
        | exact resolve b0e719 b0e619
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e719
      have b0e721 : (M.op y (M.op y y)) = (k (M.op y (M.op y y)) (M.op x y)) := by
        first
        | (have i₁ := b0e720
           have i₂ := b0e11 y y x
           grind)
        | exact superpose b0e11 b0e720
        | exact resolve b0e720 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e720
      have b0e722 : (M.op y y) = (k (M.op y y) (M.op x y)) := by
        first
        | (have i₁ := b0e721
           have i₂ := b0e138 y
           grind)
        | exact superpose b0e138 b0e721
        | exact resolve b0e721 b0e138
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e721
      have b0e723 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e722
           have i₂ := b0e619
           grind)
        | exact superpose b0e619 b0e722
        | exact resolve b0e722 b0e619
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e619 b0e722
      have b0e2210 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e74 X0 X1 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e3173 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X1) (σ X0)
           have i₂ := b0e66 X1 X0
           grind)
        | exact superpose b0e66 b0e15
        | (have j0 := b0e15 (σ X1) (σ X0)
           have j1 := b0e66 X1 X0
           grind)
        | (have r₁ := b0e15 (σ X1) (σ X1)
           have r₂ := b0e66 X1 X1
           grind)
        | (have r₁ := b0e15 (σ X0) (σ X1)
           have r₂ := b0e66 X0 X1
           grind)
        | exact resolve b0e15 b0e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3187 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e66 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e3188 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e3187 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3187
      have b0e3190 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e3173 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3173
      have b0e3191 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e3190 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3190
      have b0e3219 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e3191 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e3191
        | (have j0 := b0e3191 X0 X1
           grind)
        | exact resolve b0e3191 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3191
      have b0e49104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e3188 (M.op x y)
           have i₂ := b0e723
           grind)
        | exact superpose b0e723 b0e3188
        | (have j0 := b0e3188 (M.op x y)
           grind)
        | exact resolve b0e3188 b0e723
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e723 b0e3188
      have b0e49113 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e49104
      have b0e170521 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2210 X0 y
           have i₂ := b0e138 y
           grind)
        | exact superpose b0e138 b0e2210
        | (have j0 := b0e2210 X0 y
           grind)
        | (have r₁ := b0e2210 (M.op y (M.op (M.op y y) (M.op y y))) y
           have r₂ := b0e138 (M.op y y)
           grind)
        | (have r₁ := b0e2210 (M.op y y) y
           have r₂ := b0e138 y
           grind)
        | exact resolve b0e2210 b0e138
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e138 b0e2210
      have b0e170526 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b0e170521 X0
           have j1 := b0e16 y X0
           grind)
        | (have r₁ := b0e170521 (k y y)
           have r₂ := b0e16 y y
           grind)
        | (have r₁ := b0e170521 x
           have r₂ := b0e16 y x
           grind)
        | (have r₁ := b0e170521 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op y y)
           grind)
        | exact resolve b0e170521 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170521
      have b0e328437 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        grind
      clear b0e3219
      have b0e328694 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e328437 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e328437
        | (have j0 := b0e328437 X0 X1
           grind)
        | exact resolve b0e328437 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e328437
      have b0e328695 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e328694 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e328694
      have b0e392005 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e328695 X0 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e328695
        | exact resolve b0e328695 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e392020 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e114
           have i₂ := b0e328695 x y
           grind)
        | exact superpose b0e328695 b0e114
        | (have j1 := b0e328695 x y
           grind)
        | exact resolve b0e114 b0e328695
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114 b0e328695
      have b0e392190 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e392005 X0 X1
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e392005
        | (have j0 := b0e392005 X0 X1
           grind)
        | exact resolve b0e392005 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e392005
      have b0e392199 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e392190 X0 X1
           have i₂ := b0e25 X0 X1
           grind)
        | exact superpose b0e25 b0e392190
        | (have j0 := b0e392190 X0 X1
           grind)
        | exact resolve b0e392190 b0e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e25 b0e392190
      have b0e414998 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e392199 X0 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e392199
        | exact resolve b0e392199 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e392199
      have b0e415604 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e414998 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e414998
      have b0e415892 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op X1 y) ∨ (M.op X1 y) = (k (M.op X1 y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e415604 (M.op X1 y) X0
           have i₂ := b0e108 X1 X0
           grind)
        | exact superpose b0e108 b0e415604
        | (have j0 := b0e415604 (M.op X1 y) X0
           grind)
        | (have r₁ := b0e415604 (M.op y y) y
           have r₂ := b0e108 y y
           grind)
        | exact resolve b0e415604 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108 b0e415604
      have b0e525406 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k (M.op X0 y) x) := by
        intro X0
        first
        | (have i₁ := b0e415892 x X0
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e415892
        | (have j0 := b0e415892 x X0
           grind)
        | (have r₁ := b0e415892 x x
           have r₂ := b0e46
           grind)
        | exact resolve b0e415892 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e415892
      have b0e659987 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e392020
           grind)
        | exact superpose b0e392020 b0e18
        | exact resolve b0e18 b0e392020
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e392020
      have b0e668180 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e659987
           have i₂ := b0e170526 x
           grind)
        | exact superpose b0e170526 b0e659987
        | (have j1 := b0e170526 x
           grind)
        | exact resolve b0e659987 b0e170526
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170526 b0e659987
      have b0e668187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e668180
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e668180
        | exact resolve b0e668180 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e668180
      have b0e668188 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by grind
      clear b0e668187
      have b0e668191 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e668188
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e668188
        | exact resolve b0e668188 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e668188
      have b0e669735 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e49113
           have i₂ := b0e668191
           grind)
        | exact superpose b0e668191 b0e49113
        | exact resolve b0e49113 b0e668191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49113
      have b0e669761 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e669735
           have i₂ := b0e127
           grind)
        | exact superpose b0e127 b0e669735
        | exact resolve b0e669735 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127 b0e669735
      have b0e693618 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e669761
           grind)
        | exact superpose b0e669761 b0e18
        | exact resolve b0e18 b0e669761
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e669761
      have b0e693720 : x = (M.op x y) := by
        first
        | (have r₁ := b0e693618
           have r₂ := b0e668191
           grind)
        | exact resolve b0e693618 b0e668191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e668191 b0e693618
      have b0e695558 : x ≠ x ∨ x = (k x x) := by
        first
        | (have i₁ := b0e525406 x
           have i₂ := b0e693720
           grind)
        | exact superpose b0e693720 b0e525406
        | exact resolve b0e525406 b0e693720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e525406 b0e693720
      have b0e695704 : x = (k x x) := by grind
      clear b0e695558
      have b0e697977 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e16 x x
           have i₂ := b0e695704
           grind)
        | exact superpose b0e695704 b0e16
        | (have j0 := b0e16 x x
           grind)
        | exact resolve b0e16 b0e695704
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e695704
      have b0e697982 : x = (M.op x x) := by grind
      clear b0e697977
      have b0e699040 : x = y := by
        first
        | (have i₁ := b0e19
           have i₂ := b0e697982
           grind)
        | exact superpose b0e697982 b0e19
        | exact resolve b0e19 b0e697982
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e697982
      have b0e700696 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e699040
           grind)
        | exact superpose b0e699040 b0e18
        | exact resolve b0e18 b0e699040
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e699040
      have b0e700975 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e700696
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e700696
        | exact resolve b0e700696 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e700696
      have b0e701008 : False := by grind
      exact b0e701008
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op X1 X1) X3
             have i₂ := b1e12 (M.op X1 X1) X1 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 X2 X3
             have i₂ := b1e12 X1 X2 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X2 X2) X3 X1
             have i₂ := b1e12 X1 X2 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2 (M.op x X0)
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x X0 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op X3 X3) X1
             have i₂ := b1e12 (M.op X1 X2) X3 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 (M.op X1 X1)) X1)) := by
          intro X0 X1
          grind
        have b1e36 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e27 x X1 X2 X3
             have i₂ := b1e31 x X1 X1
             grind)
          | exact superpose b1e31 b1e27
          | exact resolve b1e27 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e31
        have b1e41 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op X0 X0) X1 x
             have i₂ := b1e33 X0
             grind)
          | exact superpose b1e33 b1e12
          | exact resolve b1e12 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e167 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 X0 (σ x) X1 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e28
          | exact resolve b1e28 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e169 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e28 X1 (M.op X0 X0) X2 x
             have i₂ := b1e33 X0
             grind)
          | exact superpose b1e33 b1e28
          | exact resolve b1e28 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e459 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X4 X0) X1) := by
          intro X0 X1 X4
          first
          | (have i₁ := b1e28 (M.op x x) X0 X1 X4
             have i₂ := b1e30 x x X0 X1
             grind)
          | exact superpose b1e30 b1e28
          | exact resolve b1e28 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e546 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (σ y) X0) X0)) := by
          intro X0
          first
          | (have i₁ := b1e35 (σ x) X0
             have i₂ := b1e32 X0
             grind)
          | exact superpose b1e32 b1e35
          | exact resolve b1e35 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e772 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (M.op (σ y) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 (σ x) X1 X0
             have i₂ := b1e32 (σ x)
             grind)
          | exact superpose b1e32 b1e36
          | exact resolve b1e36 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e787 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (M.op X1 X1) x
             have i₂ := b1e36 X1 X0 x
             grind)
          | exact superpose b1e36 b1e12
          | exact resolve b1e12 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e801 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e30 X2 X3 (M.op X0 X0) X1
             have i₂ := b1e36 X0 X0 X0
             grind)
          | exact superpose b1e36 b1e30
          | exact resolve b1e30 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e827 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e28 X1 (M.op X2 (M.op X2 X2)) X3 X4
             have i₂ := b1e36 X2 X1 X0
             grind)
          | exact superpose b1e36 b1e28
          | exact resolve b1e28 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e849 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
          intro X2 X3 X4
          first
          | (have i₁ := b1e827 x x X2 X3 X4
             have i₂ := b1e169 X2 (M.op x x) X3
             grind)
          | exact superpose b1e169 b1e827
          | exact resolve b1e827 b1e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e827
        have b1e863 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e801 X0 X1 x x
             have i₂ := b1e169 X0 (M.op x x) X1
             grind)
          | exact superpose b1e169 b1e801
          | exact resolve b1e801 b1e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e169 b1e801
        have b1e871 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e787 X0 X1
             have i₂ := b1e36 X1 X1 X1
             grind)
          | exact superpose b1e36 b1e787
          | exact resolve b1e787 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e787
        have b1e879 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e772 X0 X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e772
          | exact resolve b1e772 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e772
        have b1e910 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e863 X0 X1
             have i₂ := b1e849 X0 (M.op X1 X1) X0
             grind)
          | (have i₁ := b1e863 y X1
             have i₂ := b1e849 (M.op y (M.op y y)) (M.op X1 X1) x
             grind)
          | exact superpose b1e849 b1e863
          | exact resolve b1e863 b1e849
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e849 b1e863
        have b1e962 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b1e34 X2 (M.op x X0) (M.op X1 X1) X4
             have i₂ := b1e36 X1 X0 x
             grind)
          | exact superpose b1e36 b1e34
          | exact resolve b1e34 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1076 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e12 X3 (M.op (M.op X2 X2) (M.op X2 X2)) X4
             have i₂ := b1e34 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
             grind)
          | exact superpose b1e34 b1e12
          | exact resolve b1e12 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e1136 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e1076 X0 X1 X1 X3 X4
             have i₂ := b1e36 X1 X1 X1
             grind)
          | exact superpose b1e36 b1e1076
          | exact resolve b1e1076 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1076
        have b1e1217 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b1e962 X0 X1 X2 X4
             have i₂ := b1e41 X1 (M.op X4 X4)
             grind)
          | exact superpose b1e41 b1e962
          | exact resolve b1e962 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e962
        have b1e1248 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e1136 X0 X1 X2 X3 X4
             have i₂ := b1e871 X1 X2
             grind)
          | exact superpose b1e871 b1e1136
          | exact resolve b1e1136 b1e871
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1136
        have b1e1299 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) = (M.op (M.op y X1) X4) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b1e1217 X0 X1 X2 X4
             have i₂ := b1e910 X1 X4
             grind)
          | exact superpose b1e910 b1e1217
          | exact resolve b1e1217 b1e910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e910 b1e1217
        have b1e1319 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) = (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e1248 X0 X1 X2 X3 X4
             have i₂ := b1e871 (M.op X4 X3) X2
             grind)
          | exact superpose b1e871 b1e1248
          | exact resolve b1e1248 b1e871
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e871 b1e1248
        have b1e1364 : ∀ X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) = (M.op X3 (M.op (M.op y X2) X2)) := by
          intro X2 X3 X4
          first
          | (have i₁ := b1e1319 x x X2 X3 X4
             have i₂ := b1e1299 x X2 x X2
             grind)
          | exact superpose b1e1299 b1e1319
          | exact resolve b1e1319 b1e1299
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1299 b1e1319
        have b1e2341 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (σ x)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e30 X1 X2 (σ x) X0
             have i₂ := b1e167 (σ x) (M.op X0 X0)
             grind)
          | exact superpose b1e167 b1e30
          | exact resolve b1e30 b1e167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e2397 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e2341 X0 x x
             have i₂ := b1e167 (M.op x x) X0
             grind)
          | exact superpose b1e167 b1e2341
          | exact resolve b1e2341 b1e167
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2341
        have b1e5792 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (M.op (σ x) (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e32 (M.op X1 X1)
             have i₂ := b1e459 X1 X1 X0
             grind)
          | exact superpose b1e459 b1e32
          | exact resolve b1e32 b1e459
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e459
        have b1e5931 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ x) (M.op (M.op X0 X1) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e5792 X0 X1
             have i₂ := b1e2397 X1
             grind)
          | exact superpose b1e2397 b1e5792
          | exact resolve b1e5792 b1e2397
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5792
        have b1e9275 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e167 x (M.op (σ x) (σ x))
             have i₂ := b1e879 x (σ x)
             grind)
          | exact superpose b1e879 b1e167
          | exact resolve b1e167 b1e879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e167
        have b1e9340 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ x))) (M.op (σ x) (σ x)))) := by
          first
          | (have i₁ := b1e546 (M.op (σ x) (σ x))
             have i₂ := b1e879 (σ x) (σ x)
             grind)
          | exact superpose b1e879 b1e546
          | exact resolve b1e546 b1e879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e546 b1e879
        have b1e9390 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (M.op (σ x) (σ x))))) := by
          first
          | (have i₁ := b1e9340
             have i₂ := b1e36 (σ x) (M.op (σ x) (σ x)) (σ y)
             grind)
          | exact superpose b1e36 b1e9340
          | exact resolve b1e9340 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e9340
        have b1e9440 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e9275
             have i₂ := b1e2397 (σ x)
             grind)
          | exact superpose b1e2397 b1e9275
          | exact resolve b1e9275 b1e2397
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2397 b1e9275
        have b1e9537 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op y (σ x)) (σ x)))) := by
          first
          | (have i₁ := b1e9390
             have i₂ := b1e1364 (σ x) (σ x) (σ x)
             grind)
          | exact superpose b1e1364 b1e9390
          | exact resolve b1e9390 b1e1364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1364 b1e9390
        have b1e9578 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e9440
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e9440
          | exact resolve b1e9440 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9440
        have b1e9646 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b1e9537
             have i₂ := b1e5931 y (σ x)
             grind)
          | exact superpose b1e5931 b1e9537
          | exact resolve b1e9537 b1e5931
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5931 b1e9537
        have b1e9707 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
          first
          | (have i₁ := b1e9646
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e9646
          | exact resolve b1e9646 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9646
        have b1e9733 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e9707
             have i₂ := b1e9578
             grind)
          | exact superpose b1e9578 b1e9707
          | exact resolve b1e9707 b1e9578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9707
        have b1e9749 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e9733
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e9733
          | exact resolve b1e9733 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9733
        have b1e9771 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e9749
             grind)
          | exact superpose b1e9749 b1e13
          | exact resolve b1e13 b1e9749
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9749
        have b1e9791 : y = (k y y) := by
          first
          | (have i₁ := b1e9771
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e9771
          | exact resolve b1e9771 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9771
        have b1e9848 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e9791
             grind)
          | exact superpose b1e9791 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e9791
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9791
        have b1e9849 : y = (M.op y y) := by grind
        clear b1e9848
        have b1e9919 : y = (M.op x y) := by
          first
          | (have i₁ := b1e33 y
             have i₂ := b1e9849
             grind)
          | exact superpose b1e9849 b1e33
          | exact resolve b1e33 b1e9849
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e9849
        have b1e10116 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e9578
             grind)
          | exact superpose b1e9578 b1e19
          | exact resolve b1e19 b1e9578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9578
        have b1e10134 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e10116
             have i₂ := b1e9919
             grind)
          | exact superpose b1e9919 b1e10116
          | exact resolve b1e10116 b1e9919
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9919 b1e10116
        have b1e10135 : False := by grind
        exact b1e10135
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b2e24 : x = (k x y) := by grind
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 (M.op X1 X1) X3
             have i₂ := b2e12 (M.op X1 X1) X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X2 X3
             have i₂ := b2e12 X1 X2 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X2 X2) X3 X1
             have i₂ := b2e12 X1 X2 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 (M.op x X0)
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
          intro X1 X2 X3
          first
          | (have i₁ := b2e27 x X1 X2 X3
             have i₂ := b2e32 x X1 X1
             grind)
          | exact superpose b2e32 b2e27
          | exact resolve b2e27 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e32
        have b2e40 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op X0 X0) X1 x
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e415 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X2 X2) (M.op (M.op (M.op X0 X1) X2) X2)) := by
          intro X0 X1 X2
          grind
        have b2e733 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) X1) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e31 X2 X3 X0 X1
             have i₂ := b2e35 X1 X0 X0
             grind)
          | exact superpose b2e35 b2e31
          | exact resolve b2e31 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1402 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e64 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e1403 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1402
             have r₂ := b2e22
             grind)
          | exact resolve b2e1402 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1402
        have b2e1404 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1403
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1403
          | exact resolve b2e1403 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1403
        have b2e1405 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1404
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1404
          | exact resolve b2e1404 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1404
        have b2e1407 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 (σ y) X0 (σ x)
             have i₂ := b2e1405
             grind)
          | exact superpose b2e1405 b2e12
          | exact resolve b2e12 b2e1405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1410 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X0 (σ y) X1 (σ x)
             have i₂ := b2e1405
             grind)
          | exact superpose b2e1405 b2e28
          | exact resolve b2e28 b2e1405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e3019 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e35 X1 X0 X0
             have i₂ := b2e40 X0 X1
             grind)
          | exact superpose b2e40 b2e35
          | exact resolve b2e35 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e3814 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (σ y)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31 X1 X2 (σ y) X0
             have i₂ := b2e1410 (σ y) (M.op X0 X0)
             grind)
          | exact superpose b2e1410 b2e31
          | exact resolve b2e31 b2e1410
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e3891 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3814 X0 x x
             have i₂ := b2e1410 (M.op x x) X0
             grind)
          | exact superpose b2e1410 b2e3814
          | exact resolve b2e3814 b2e1410
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1410 b2e3814
        have b2e15171 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) X2) (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e733 X2 (σ y) X0 X1
             have i₂ := b2e1407 (σ y)
             grind)
          | exact superpose b2e1407 b2e733
          | exact resolve b2e733 b2e1407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e733
        have b2e15624 : ∀ X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ y) (σ y))) := by
          intro X2
          first
          | (have i₁ := b2e15171 x x X2
             have i₂ := b2e12 X2 (σ y) (M.op x x)
             grind)
          | exact superpose b2e12 b2e15171
          | exact resolve b2e15171 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15171
        have b2e15855 : ∀ X2 : G, (M.op X2 (σ x)) = (M.op X2 (M.op (σ y) (σ y))) := by
          intro X2
          first
          | (have i₁ := b2e15624 X2
             have i₂ := b2e1405
             grind)
          | exact superpose b2e1405 b2e15624
          | exact resolve b2e15624 b2e1405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15624
        have b2e16140 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X1 X0) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 (σ y) X1
             have i₂ := b2e15855 X0
             grind)
          | exact superpose b2e15855 b2e12
          | exact resolve b2e12 b2e15855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e16248 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (M.op (M.op X0 X1) (σ x)) (M.op (σ y) (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e415 X0 X1 (M.op (σ y) (σ y))
             have i₂ := b2e15855 (M.op X0 X1)
             grind)
          | exact superpose b2e15855 b2e415
          | exact resolve b2e415 b2e15855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e415
        have b2e16274 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e1407 (σ y)
             have i₂ := b2e15855 (σ y)
             grind)
          | exact superpose b2e15855 b2e1407
          | exact resolve b2e1407 b2e15855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1407
        have b2e16275 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e3891 (σ y)
             have i₂ := b2e15855 (σ x)
             grind)
          | exact superpose b2e15855 b2e3891
          | exact resolve b2e3891 b2e15855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3891 b2e15855
        have b2e16289 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e16275
             have i₂ := b2e1405
             grind)
          | exact superpose b2e1405 b2e16275
          | exact resolve b2e16275 b2e1405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16275
        have b2e16290 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e16274
             have i₂ := b2e1405
             grind)
          | exact superpose b2e1405 b2e16274
          | exact resolve b2e16274 b2e1405
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1405 b2e16274
        have b2e16315 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y))))) := by
          first
          | (have i₁ := b2e16248 x x
             have i₂ := b2e35 (σ y) (σ x) (M.op x x)
             grind)
          | exact superpose b2e35 b2e16248
          | exact resolve b2e16248 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16248
        have b2e16484 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (M.op y (σ x)) (σ y))) := by
          first
          | (have i₁ := b2e16315
             have i₂ := b2e3019 (σ x) (σ y)
             grind)
          | exact superpose b2e3019 b2e16315
          | exact resolve b2e16315 b2e3019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16315
        have b2e16627 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b2e16484
             have i₂ := b2e16140 (σ x) y
             grind)
          | exact superpose b2e16140 b2e16484
          | exact resolve b2e16484 b2e16140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16484
        have b2e16707 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (σ x)) := by
          first
          | (have i₁ := b2e16627
             have i₂ := b2e16289
             grind)
          | exact superpose b2e16289 b2e16627
          | exact resolve b2e16627 b2e16289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16627
        have b2e16759 : (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) = (k (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) (σ x)) := by
          first
          | (have i₁ := b2e16707
             have i₂ := b2e35 (σ y) (σ y) (σ y)
             grind)
          | exact superpose b2e35 b2e16707
          | exact resolve b2e16707 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e16707
        have b2e16784 : (M.op (M.op y (σ y)) (σ y)) = (k (M.op (M.op y (σ y)) (σ y)) (σ x)) := by
          first
          | (have i₁ := b2e16759
             have i₂ := b2e3019 (σ y) (σ y)
             grind)
          | exact superpose b2e3019 b2e16759
          | exact resolve b2e16759 b2e3019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3019 b2e16759
        have b2e16802 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ x)) := by
          first
          | (have i₁ := b2e16784
             have i₂ := b2e16140 (σ y) y
             grind)
          | exact superpose b2e16140 b2e16784
          | exact resolve b2e16784 b2e16140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16140 b2e16784
        have b2e16814 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b2e16802
             have i₂ := b2e16290
             grind)
          | exact superpose b2e16290 b2e16802
          | exact resolve b2e16802 b2e16290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16290 b2e16802
        have b2e16825 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e16814
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e16814
          | exact resolve b2e16814 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16814
        have b2e17968 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b2e13 (k x x)
             have i₂ := b2e16825
             grind)
          | exact superpose b2e16825 b2e13
          | exact resolve b2e13 b2e16825
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16825
        have b2e18004 : x = (k x x) := by
          first
          | (have i₁ := b2e17968
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e17968
          | exact resolve b2e17968 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17968
        have b2e19484 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e18004
             grind)
          | exact superpose b2e18004 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e18004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18004
        have b2e19485 : x = (M.op x x) := by grind
        clear b2e19484
        have b2e19867 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e19485
             grind)
          | exact superpose b2e19485 b2e20
          | exact resolve b2e20 b2e19485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19485
        have b2e20734 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e19867
             grind)
          | exact superpose b2e19867 b2e22
          | exact resolve b2e22 b2e19867
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19867
        have b2e20776 : False := by grind
        exact b2e20776
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op X1 X1) X3
             have i₂ := b3e12 (M.op X1 X1) X1 X0
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X2 X2) X3 X1
             have i₂ := b3e12 X1 X2 X0
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 (M.op x X0)
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e40 x X1 X2 X3
             have i₂ := b3e45 x X1 X1
             grind)
          | exact superpose b3e45 b3e40
          | exact resolve b3e40 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e45
        have b3e54 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 x X0 X1
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e12
          | exact resolve b3e12 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e465 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e54 (M.op X2 X2) x
             have i₂ := b3e44 X0 X1 x X2
             grind)
          | exact superpose b3e44 b3e54
          | exact resolve b3e54 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e501 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
          intro X2
          first
          | (have i₁ := b3e465 x x X2
             have i₂ := b3e54 X2 (M.op x x)
             grind)
          | exact superpose b3e54 b3e465
          | exact resolve b3e465 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e465
        have b3e731 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x (M.op X0 (M.op X0 (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b3e47 (M.op X0 X0)
             have i₂ := b3e50 X0 X0 X0
             grind)
          | exact superpose b3e50 b3e47
          | exact resolve b3e47 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e746 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op X1 X1) x
             have i₂ := b3e50 X1 X0 x
             grind)
          | exact superpose b3e50 b3e12
          | exact resolve b3e12 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e792 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e746 X0 X1
             have i₂ := b3e50 X1 X1 X1
             grind)
          | exact superpose b3e50 b3e746
          | exact resolve b3e746 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e746
        have b3e801 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 (M.op X0 (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b3e731 X0
             have i₂ := b3e501 X0
             grind)
          | (have i₁ := b3e731 X0
             have i₂ := b3e501 (M.op X0 X0)
             grind)
          | exact superpose b3e501 b3e731
          | exact resolve b3e731 b3e501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e501 b3e731
        have b3e843 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b3e801 X0
             have i₂ := b3e792 x X0
             grind)
          | exact superpose b3e792 b3e801
          | exact resolve b3e801 b3e792
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e792 b3e801
        have b3e2609 : (M.op y x) = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b3e843 x
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e843
          | exact resolve b3e843 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e843
        have b3e2639 : y = (M.op x y) := by
          first
          | (have i₁ := b3e2609
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e2609
          | exact resolve b3e2609 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2609
        have b3e2949 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e74 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e74
          | exact resolve b3e74 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e3089 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e2949
        have b3e3691 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e3089
             grind)
          | exact superpose b3e3089 b3e13
          | exact resolve b3e13 b3e3089
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3089
        have b3e3711 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e3691
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e3691
          | exact resolve b3e3691 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3691
        have b3e3719 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e3711
             grind)
          | exact superpose b3e3711 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e3711
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3711
        have b3e3720 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e3719
        have b3e3722 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e3720
             have r₂ := b3e20
             grind)
          | exact resolve b3e3720 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3720
        have b3e3970 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e47 x
             have i₂ := b3e3722
             grind)
          | exact superpose b3e3722 b3e47
          | exact resolve b3e47 b3e3722
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e3722
        have b3e4000 : y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e3970
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3970
          | exact resolve b3e3970 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3970
        have b3e4004 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e4000
             have r₂ := b3e20
             grind)
          | exact resolve b3e4000 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4000
        have b3e4136 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e4004
             grind)
          | exact superpose b3e4004 b3e19
          | exact resolve b3e19 b3e4004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4170 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e4136
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e4136
          | exact resolve b3e4136 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4136
        have b3e4176 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e4170
             have i₂ := b3e4004
             grind)
          | exact superpose b3e4004 b3e4170
          | exact resolve b3e4170 b3e4004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4170
        have b3e4182 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e4176
             have i₂ := b3e2639
             grind)
          | exact superpose b3e2639 b3e4176
          | exact resolve b3e4176 b3e2639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2639 b3e4176
        have b3e4184 : False := by grind
        exact b3e4184
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X1 X1) X3
               have i₂ := b4e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X2 X2) X3 X1
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op x X0)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
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
          have b4e34 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
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
          have b4e37 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e28 x X1 X2 X3
               have i₂ := b4e32 x X1 X1
               grind)
            | exact superpose b4e32 b4e28
            | exact resolve b4e28 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e32
          have b4e40 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e34 X0
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e123 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e29 X0 (σ x) X1 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e29
            | exact resolve b4e29 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e358 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e40 (M.op X2 X2) x
               have i₂ := b4e31 X0 X1 x X2
               grind)
            | exact superpose b4e31 b4e40
            | exact resolve b4e40 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e388 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
            intro X2
            first
            | (have i₁ := b4e358 x x X2
               have i₂ := b4e40 X2 (M.op x x)
               grind)
            | exact superpose b4e40 b4e358
            | exact resolve b4e358 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e358
          have b4e568 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b4e37 (σ x) X1 X0
               have i₂ := b4e33 (σ x)
               grind)
            | exact superpose b4e33 b4e37
            | exact resolve b4e37 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e591 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e34 (M.op X0 X0)
               have i₂ := b4e37 X0 X0 X0
               grind)
            | exact superpose b4e37 b4e34
            | exact resolve b4e34 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e605 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X1 X1) x
               have i₂ := b4e37 X1 X0 x
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e649 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e605 X0 X1
               have i₂ := b4e37 X1 X1 X1
               grind)
            | exact superpose b4e37 b4e605
            | exact resolve b4e605 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e605
          have b4e657 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e591 X0
               have i₂ := b4e388 X0
               grind)
            | (have i₁ := b4e591 X0
               have i₂ := b4e388 (M.op X0 X0)
               grind)
            | exact superpose b4e388 b4e591
            | exact resolve b4e591 b4e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e388 b4e591
          have b4e669 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e568 X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e568
            | exact resolve b4e568 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e568
          have b4e695 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e657 X0
               have i₂ := b4e649 x X0
               grind)
            | exact superpose b4e649 b4e657
            | exact resolve b4e657 b4e649
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e649 b4e657
          have b4e1243 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (σ x)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e31 X1 X2 (σ x) X0
               have i₂ := b4e123 (σ x) (M.op X0 X0)
               grind)
            | exact superpose b4e123 b4e31
            | exact resolve b4e31 b4e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e1260 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1243 X0 x x
               have i₂ := b4e123 (M.op x x) X0
               grind)
            | exact superpose b4e123 b4e1243
            | exact resolve b4e1243 b4e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1243
          have b4e1301 : (M.op y x) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e695 x
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e695
            | exact resolve b4e695 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e695
          have b4e1320 : y = (M.op x y) := by
            first
            | (have i₁ := b4e1301
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1301
            | exact resolve b4e1301 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1301
          have b4e7768 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b4e123 x (M.op (σ x) (σ x))
               have i₂ := b4e669 x (σ x)
               grind)
            | exact superpose b4e669 b4e123
            | exact resolve b4e123 b4e669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123 b4e669
          have b4e7841 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e7768
               have i₂ := b4e1260 (σ x)
               grind)
            | exact superpose b4e1260 b4e7768
            | exact resolve b4e7768 b4e1260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1260 b4e7768
          have b4e7977 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e7841
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e7841
            | exact resolve b4e7841 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7841
          have b4e8209 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e7977
               grind)
            | exact superpose b4e7977 b4e20
            | exact resolve b4e20 b4e7977
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7977
          have b4e8226 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e8209
               have i₂ := b4e1320
               grind)
            | exact superpose b4e1320 b4e8209
            | exact resolve b4e8209 b4e1320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1320 b4e8209
          have b4e8227 : False := by grind
          exact b4e8227
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
          have b5e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X1 X1) X3
               have i₂ := b5e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X2) X3 X1
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op x X0)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X3 X3) X1
               have i₂ := b5e13 (M.op X1 X2) X3 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e28 x X1 X2 X3
               have i₂ := b5e33 x X1 X1
               grind)
            | exact superpose b5e33 b5e28
            | exact resolve b5e28 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e33
          have b5e40 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X0) X1 x
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e46 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e45
          have b5e47 : x = (k x y) := by
            first
            | (have r₁ := b5e46
               have r₂ := b5e21
               grind)
            | exact resolve b5e46 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e117 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29 X1 (M.op X0 X0) X2 x
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e29
            | exact resolve b5e29 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e304 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X2 X2) (M.op (M.op (M.op X0 X1) X2) X2)) := by
            intro X0 X1 X2
            grind
          have b5e523 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) X1) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e32 X2 X3 X0 X1
               have i₂ := b5e36 X1 X0 X0
               grind)
            | exact superpose b5e36 b5e32
            | exact resolve b5e32 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e532 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e32 X2 X3 (M.op X0 X0) X1
               have i₂ := b5e36 X0 X0 X0
               grind)
            | exact superpose b5e36 b5e32
            | exact resolve b5e32 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e549 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X1 X1) x
               have i₂ := b5e36 X1 X0 x
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e564 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e29 X1 (M.op X2 (M.op X2 X2)) X3 X4
               have i₂ := b5e36 X2 X1 X0
               grind)
            | exact superpose b5e36 b5e29
            | exact resolve b5e29 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e584 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e564 x x X2 X3 X4
               have i₂ := b5e117 X2 (M.op x x) X3
               grind)
            | exact superpose b5e117 b5e564
            | exact resolve b5e564 b5e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e564
          have b5e592 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e549 X0 X1
               have i₂ := b5e36 X1 X1 X1
               grind)
            | exact superpose b5e36 b5e549
            | exact resolve b5e549 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e549
          have b5e602 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e532 X0 X1 x x
               have i₂ := b5e117 X0 (M.op x x) X1
               grind)
            | exact superpose b5e117 b5e532
            | exact resolve b5e532 b5e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e117 b5e532
          have b5e636 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e602 X0 X1
               have i₂ := b5e584 X0 (M.op X1 X1) X0
               grind)
            | (have i₁ := b5e602 y X1
               have i₂ := b5e584 (M.op y (M.op y y)) (M.op X1 X1) x
               grind)
            | exact superpose b5e584 b5e602
            | exact resolve b5e602 b5e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e584 b5e602
          have b5e686 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e34 X2 (M.op x X0) (M.op X1 X1) X4
               have i₂ := b5e36 X1 X0 x
               grind)
            | exact superpose b5e36 b5e34
            | exact resolve b5e34 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e786 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X3 (M.op (M.op X2 X2) (M.op X2 X2)) X4
               have i₂ := b5e34 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e836 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e786 X0 X1 X1 X3 X4
               have i₂ := b5e36 X1 X1 X1
               grind)
            | exact superpose b5e36 b5e786
            | exact resolve b5e786 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e786
          have b5e905 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e686 X0 X1 X2 X4
               have i₂ := b5e40 X1 (M.op X4 X4)
               grind)
            | exact superpose b5e40 b5e686
            | exact resolve b5e686 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e686
          have b5e934 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e836 X0 X1 X2 X3 X4
               have i₂ := b5e592 X1 X2
               grind)
            | exact superpose b5e592 b5e836
            | exact resolve b5e836 b5e592
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e836
          have b5e976 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) = (M.op (M.op y X1) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e905 X0 X1 X2 X4
               have i₂ := b5e636 X1 X4
               grind)
            | exact superpose b5e636 b5e905
            | exact resolve b5e905 b5e636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e636 b5e905
          have b5e995 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) = (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e934 X0 X1 X2 X3 X4
               have i₂ := b5e592 (M.op X4 X3) X2
               grind)
            | exact superpose b5e592 b5e934
            | exact resolve b5e934 b5e592
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e934
          have b5e1033 : ∀ X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) = (M.op X3 (M.op (M.op y X2) X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e995 x x X2 X3 X4
               have i₂ := b5e976 x X2 x X2
               grind)
            | exact superpose b5e976 b5e995
            | exact resolve b5e995 b5e976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e976 b5e995
          have b5e1141 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e1142 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1141
               have r₂ := b5e24
               grind)
            | exact resolve b5e1141 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1141
          have b5e1143 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1142
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1142
            | exact resolve b5e1142 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1142
          have b5e1144 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1143
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e1143
            | exact resolve b5e1143 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e1143
          have b5e1146 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 (σ y) X0 (σ x)
               have i₂ := b5e1144
               grind)
            | exact superpose b5e1144 b5e13
            | exact resolve b5e13 b5e1144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1149 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e29 X0 (σ y) X1 (σ x)
               have i₂ := b5e1144
               grind)
            | exact superpose b5e1144 b5e29
            | exact resolve b5e29 b5e1144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2744 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 X1 (M.op X0 X0)
               have i₂ := b5e36 X0 X0 X0
               grind)
            | exact superpose b5e36 b5e40
            | exact resolve b5e40 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2826 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e29 X0 X0 (M.op X1 X1) X2
               have i₂ := b5e40 X0 X1
               grind)
            | exact superpose b5e40 b5e29
            | exact resolve b5e29 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29 b5e40
          have b5e2866 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2744 X0 X1
               have i₂ := b5e2826 X1 X0 y
               grind)
            | exact superpose b5e2826 b5e2744
            | exact resolve b5e2744 b5e2826
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2744 b5e2826
          have b5e2889 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2866 X0 X1
               have i₂ := b5e592 (M.op X1 X1) X0
               grind)
            | exact superpose b5e592 b5e2866
            | exact resolve b5e2866 b5e592
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e592 b5e2866
          have b5e2902 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X1 (M.op (M.op y X0) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2889 X0 X1
               have i₂ := b5e1033 X0 X1 X1
               grind)
            | exact superpose b5e1033 b5e2889
            | exact resolve b5e2889 b5e1033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2889
          have b5e3127 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (σ y)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e32 X1 X2 (σ y) X0
               have i₂ := b5e1149 (σ y) (M.op X0 X0)
               grind)
            | exact superpose b5e1149 b5e32
            | exact resolve b5e32 b5e1149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e3154 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e3127 X0 x x
               have i₂ := b5e1149 (M.op x x) X0
               grind)
            | exact superpose b5e1149 b5e3127
            | exact resolve b5e3127 b5e1149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1149 b5e3127
          have b5e14338 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) X2) (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e523 X2 (σ y) X0 X1
               have i₂ := b5e1146 (σ y)
               grind)
            | exact superpose b5e1146 b5e523
            | exact resolve b5e523 b5e1146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e523
          have b5e14785 : ∀ X2 : G, (M.op X2 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ y) (σ y))) := by
            intro X2
            first
            | (have i₁ := b5e14338 x x X2
               have i₂ := b5e13 X2 (σ y) (M.op x x)
               grind)
            | exact superpose b5e13 b5e14338
            | exact resolve b5e14338 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14338
          have b5e15017 : ∀ X2 : G, (M.op X2 (σ x)) = (M.op X2 (M.op (σ y) (σ y))) := by
            intro X2
            first
            | (have i₁ := b5e14785 X2
               have i₂ := b5e1144
               grind)
            | exact superpose b5e1144 b5e14785
            | exact resolve b5e14785 b5e1144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14785
          have b5e17970 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X1 X0) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (σ y) X1
               have i₂ := b5e15017 X0
               grind)
            | exact superpose b5e15017 b5e13
            | exact resolve b5e13 b5e15017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e17994 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e1146 (σ y)
               have i₂ := b5e15017 (σ y)
               grind)
            | exact superpose b5e15017 b5e1146
            | exact resolve b5e1146 b5e15017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e17995 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e3154 (σ y)
               have i₂ := b5e15017 (σ x)
               grind)
            | exact superpose b5e15017 b5e3154
            | exact resolve b5e3154 b5e15017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3154
          have b5e18023 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ y) (σ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e304 X0 X1 (M.op (σ y) (σ y))
               have i₂ := b5e15017 (M.op (σ y) (σ y))
               grind)
            | exact superpose b5e15017 b5e304
            | exact resolve b5e304 b5e15017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e304 b5e15017
          have b5e18205 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
            first
            | (have i₁ := b5e18023 x x
               have i₂ := b5e36 (σ y) (M.op (σ y) (σ y)) (M.op x x)
               grind)
            | exact superpose b5e36 b5e18023
            | exact resolve b5e18023 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e18023
          have b5e18232 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e17995
               have i₂ := b5e1144
               grind)
            | exact superpose b5e1144 b5e17995
            | exact resolve b5e17995 b5e1144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17995
          have b5e18233 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e17994
               have i₂ := b5e1144
               grind)
            | exact superpose b5e1144 b5e17994
            | exact resolve b5e17994 b5e1144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1144 b5e17994
          have b5e18380 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (σ y) (M.op (M.op y (σ y)) (σ y)))) := by
            first
            | (have i₁ := b5e18205
               have i₂ := b5e1033 (σ y) (σ y) (σ y)
               grind)
            | exact superpose b5e1033 b5e18205
            | exact resolve b5e18205 b5e1033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1033 b5e18205
          have b5e18506 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (M.op y (σ y)) (σ y))) := by
            first
            | (have i₁ := b5e18380
               have i₂ := b5e2902 (σ y) (σ y)
               grind)
            | exact superpose b5e2902 b5e18380
            | exact resolve b5e18380 b5e2902
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2902 b5e18380
          have b5e18581 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e18506
               have i₂ := b5e17970 (σ y) y
               grind)
            | exact superpose b5e17970 b5e18506
            | exact resolve b5e18506 b5e17970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17970 b5e18506
          have b5e18630 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ x)) (σ x)) := by
            first
            | (have i₁ := b5e18581
               have i₂ := b5e18233
               grind)
            | exact superpose b5e18233 b5e18581
            | exact resolve b5e18581 b5e18233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18233 b5e18581
          have b5e18661 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (M.op (σ x) (σ x))) (σ x)) := by
            first
            | (have i₁ := b5e18630
               have i₂ := b5e13 (σ y) (σ x) (σ y)
               grind)
            | exact superpose b5e13 b5e18630
            | exact resolve b5e18630 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18630
          have b5e18682 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
            first
            | (have i₁ := b5e18661
               have i₂ := b5e1146 (σ x)
               grind)
            | exact superpose b5e1146 b5e18661
            | exact resolve b5e18661 b5e1146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1146 b5e18661
          have b5e18696 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b5e18682
               have i₂ := b5e18232
               grind)
            | exact superpose b5e18232 b5e18682
            | exact resolve b5e18682 b5e18232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18232 b5e18682
          have b5e18706 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b5e18696
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e18696
            | exact resolve b5e18696 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18696
          have b5e19064 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 (k x x)
               have i₂ := b5e18706
               grind)
            | exact superpose b5e18706 b5e14
            | exact resolve b5e14 b5e18706
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18706
          have b5e19100 : x = (k x x) := by
            first
            | (have i₁ := b5e19064
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e19064
            | exact resolve b5e19064 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19064
          have b5e19771 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e19100
               grind)
            | exact superpose b5e19100 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e19100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19100
          have b5e19772 : x = (M.op x x) := by grind
          clear b5e19771
          have b5e20463 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b5e31 x
               have i₂ := b5e19772
               grind)
            | exact superpose b5e19772 b5e31
            | exact resolve b5e31 b5e19772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e19772
          have b5e20535 : y = (M.op x x) := by
            first
            | (have i₁ := b5e20463
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20463
            | exact resolve b5e20463 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20463
          have b5e20547 : False := by grind
          exact b5e20547
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e82 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e91 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e82
             have r₂ := b6e20
             grind)
          | exact resolve b6e82 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e95 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e91
             have r₂ := b6e21
             grind)
          | exact resolve b6e91 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e2504 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e79 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e79
          | exact resolve b6e79 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e2637 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e2504
        have b6e3352 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e2637
             grind)
          | exact superpose b6e2637 b6e13
          | exact resolve b6e13 b6e2637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3372 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3352
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3352
          | exact resolve b6e3352 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3352
        have b6e3380 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e3372
             grind)
          | exact superpose b6e3372 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e3372
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3372
        have b6e3381 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3380
        have b6e3383 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3381
             have r₂ := b6e20
             grind)
          | exact resolve b6e3381 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3381
        have b6e3733 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3383
        have b6e4423 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2637
             have i₂ := b6e3733
             grind)
          | exact superpose b6e3733 b6e2637
          | exact resolve b6e2637 b6e3733
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2637 b6e3733
        have b6e4430 : (σ x) = (σ y) := by grind
        clear b6e4423
        have b6e4544 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e4430
             grind)
          | exact superpose b6e4430 b6e19
          | exact resolve b6e19 b6e4430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4575 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e4544
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4544
          | exact resolve b6e4544 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4544
        have b6e4581 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4575
             have i₂ := b6e4430
             grind)
          | exact superpose b6e4430 b6e4575
          | exact resolve b6e4575 b6e4430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4430 b6e4575
        have b6e4587 : False := by grind
        exact b6e4587
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
          have b7e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X1 X1) X3
               have i₂ := b7e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X3
               have i₂ := b7e13 X1 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 X2) X3 X1
               have i₂ := b7e13 X1 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op x X0)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1
            grind
          have b7e36 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e28 x X1 X2 X3
               have i₂ := b7e33 x X1 X1
               grind)
            | exact superpose b7e33 b7e28
            | exact resolve b7e28 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e49 : (σ x) = (σ (k x y)) := by
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
          have b7e52 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : x = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e74 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e75 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e21
               grind)
            | exact resolve b7e74 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e77 : x = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e89 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e13
            | exact resolve b7e13 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e108 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e29 X0 (σ x) X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e109 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e29 X0 y X1 x
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e29
            | exact resolve b7e29 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e135 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 (M.op X1 X1)
               have i₂ := b7e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e146 : ∀ X1 : G, (M.op (σ y) (M.op X1 X1)) = (M.op (σ x) (M.op X1 (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b7e135 x X1
               have i₂ := b7e33 x X1 X1
               grind)
            | exact superpose b7e33 b7e135
            | exact resolve b7e135 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135
          have b7e192 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (M.op (σ x) (σ x))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 X1
               have i₂ := b7e33 X0 (σ x) X1
               grind)
            | exact superpose b7e33 b7e31
            | exact resolve b7e31 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e325 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e109 (M.op x x) X0
               have i₂ := b7e32 x x y X0
               grind)
            | exact superpose b7e32 b7e109
            | exact resolve b7e109 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e343 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e325 X0
               have i₂ := b7e109 y (M.op X0 X0)
               grind)
            | exact superpose b7e109 b7e325
            | exact resolve b7e325 b7e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109 b7e325
          have b7e396 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (σ y) X0) X0)) := by
            intro X0
            first
            | (have i₁ := b7e35 (σ x) X0
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e35
            | exact resolve b7e35 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e35
          have b7e541 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b7e89 (M.op X0 X0)
               have i₂ := b7e36 X0 X0 X0
               grind)
            | exact superpose b7e36 b7e89
            | exact resolve b7e89 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e554 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (M.op X1 X1) x
               have i₂ := b7e36 X1 X0 x
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e590 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e554 X0 X1
               have i₂ := b7e36 X1 X1 X1
               grind)
            | exact superpose b7e36 b7e554
            | exact resolve b7e554 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e554
          have b7e596 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b7e541 X0
               have i₂ := b7e343 X0
               grind)
            | exact superpose b7e343 b7e541
            | exact resolve b7e541 b7e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e343 b7e541
          have b7e621 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e596 X0
               have i₂ := b7e590 y X0
               grind)
            | exact superpose b7e590 b7e596
            | exact resolve b7e596 b7e590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e590 b7e596
          have b7e1754 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (σ x)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e32 X1 X2 (σ x) X0
               have i₂ := b7e108 (σ x) (M.op X0 X0)
               grind)
            | exact superpose b7e108 b7e32
            | exact resolve b7e32 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e1773 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e1754 X0 x x
               have i₂ := b7e108 (M.op x x) X0
               grind)
            | exact superpose b7e108 b7e1754
            | exact resolve b7e1754 b7e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108 b7e1754
          have b7e2812 : (M.op x y) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b7e621 y
               have i₂ := b7e89 y
               grind)
            | exact superpose b7e89 b7e621
            | exact resolve b7e621 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e621
          have b7e2837 : x = (M.op y x) := by
            first
            | (have i₁ := b7e2812
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e2812
            | exact resolve b7e2812 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2812
          have b7e3178 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e2837
               grind)
            | exact superpose b7e2837 b7e22
            | exact resolve b7e22 b7e2837
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2837
          have b7e5071 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ y) (M.op (σ x) (σ x)))) := by
            first
            | (have i₁ := b7e396 (M.op (σ x) (σ x))
               have i₂ := b7e192 (σ y) (M.op (σ x) (σ x))
               grind)
            | exact superpose b7e192 b7e396
            | exact resolve b7e396 b7e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e192 b7e396
          have b7e5115 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b7e5071
               have i₂ := b7e1773 (σ x)
               grind)
            | exact superpose b7e1773 b7e5071
            | exact resolve b7e5071 b7e1773
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5071
          have b7e5151 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ y)) := by
            first
            | (have i₁ := b7e5115
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e5115
            | exact resolve b7e5115 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5115
          have b7e5183 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) = (k (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) (σ y)) := by
            first
            | (have i₁ := b7e5151
               have i₂ := b7e36 (σ x) (σ x) (σ x)
               grind)
            | exact superpose b7e36 b7e5151
            | exact resolve b7e5151 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e5151
          have b7e5212 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (M.op (σ x) (σ x))) (σ y)) := by
            first
            | (have i₁ := b7e5183
               have i₂ := b7e146 (σ x)
               grind)
            | exact superpose b7e146 b7e5183
            | exact resolve b7e5183 b7e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e146 b7e5183
          have b7e5225 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e5212
               have i₂ := b7e1773 (σ x)
               grind)
            | exact superpose b7e1773 b7e5212
            | exact resolve b7e5212 b7e1773
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1773 b7e5212
          have b7e5233 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e5225
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e5225
            | exact resolve b7e5225 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5225
          have b7e5241 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e5233
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e5233
            | exact resolve b7e5233 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5233
          have b7e6326 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e5241
               grind)
            | exact superpose b7e5241 b7e14
            | exact resolve b7e14 b7e5241
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5241
          have b7e6346 : y = (k y y) := by
            first
            | (have i₁ := b7e6326
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e6326
            | exact resolve b7e6326 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6326
          have b7e6404 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e6346
               grind)
            | exact superpose b7e6346 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e6346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6346
          have b7e6405 : y = (M.op y y) := by grind
          clear b7e6404
          have b7e6487 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e89 y
               have i₂ := b7e6405
               grind)
            | exact superpose b7e6405 b7e89
            | exact resolve b7e89 b7e6405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e6521 : y = (M.op x y) := by
            first
            | (have i₁ := b7e6487
               have i₂ := b7e6405
               grind)
            | exact superpose b7e6405 b7e6487
            | exact resolve b7e6487 b7e6405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6405 b7e6487
          have b7e6526 : x = y := by
            first
            | (have i₁ := b7e6521
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e6521
            | exact resolve b7e6521 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e6521
          have b7e6529 : False := by grind
          exact b7e6529
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
          have b8e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e1347 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e65 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e1348 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1347
               have r₂ := b8e24
               grind)
            | exact resolve b8e1347 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1347
          have b8e1349 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1348
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1348
            | exact resolve b8e1348 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1348
          have b8e1350 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1349
               grind)
            | exact superpose b8e1349 b8e20
            | exact resolve b8e20 b8e1349
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1349
          have b8e1628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1350
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1350
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1350 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1350
          have b8e1629 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e1628
          have b8e1631 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1629
               have r₂ := b8e21
               grind)
            | exact resolve b8e1629 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1629
          have b8e1633 : False := by grind
          exact b8e1633

/-- `Equation4490`: `x ◇ (y ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation4490 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4490 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4490.models_iff G M).mp hM
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
      have b0e64 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e67 : False := by grind
      exact b0e67
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X1 X1) X3
               have i₂ := b4e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X2 X2) X3 X1
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op x X0)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
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
          have b4e38 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
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
          have b4e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X3 X3) X1
               have i₂ := b4e13 (M.op X1 X2) X3 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e32 x X1 X2 X3
               have i₂ := b4e36 x X1 X1
               grind)
            | exact superpose b4e36 b4e32
            | exact resolve b4e32 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e36
          have b4e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 X0) X1 x
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 X1 (M.op x X0)
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e43
            | exact resolve b4e43 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 X1 (M.op X0 X0) X2 x
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e33
            | exact resolve b4e33 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e172 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e37 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e37
            | exact resolve b4e37 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e354 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e43 (M.op X2 X2) x
               have i₂ := b4e35 X0 X1 x X2
               grind)
            | exact superpose b4e35 b4e43
            | exact resolve b4e43 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e388 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
            intro X2
            first
            | (have i₁ := b4e354 x x X2
               have i₂ := b4e43 X2 (M.op x x)
               grind)
            | exact superpose b4e43 b4e354
            | exact resolve b4e354 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e354
          have b4e477 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X1 X1) x
               have i₂ := b4e40 X1 X0 x
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e485 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 X3 (M.op X0 X0) X1
               have i₂ := b4e40 X0 X0 X0
               grind)
            | exact superpose b4e40 b4e35
            | exact resolve b4e35 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e491 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e388 (M.op X0 X0)
               have i₂ := b4e40 X0 X0 X0
               grind)
            | exact superpose b4e40 b4e388
            | exact resolve b4e388 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e507 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e33 X1 (M.op X2 (M.op X2 X2)) X3 X4
               have i₂ := b4e40 X2 X1 X0
               grind)
            | exact superpose b4e40 b4e33
            | exact resolve b4e33 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e522 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
            intro X2 X3 X4
            first
            | (have i₁ := b4e507 x x X2 X3 X4
               have i₂ := b4e130 X2 (M.op x x) X3
               grind)
            | exact superpose b4e130 b4e507
            | exact resolve b4e507 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e507
          have b4e530 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e491 X0
               have i₂ := b4e388 X0
               grind)
            | (have i₁ := b4e491 X0
               have i₂ := b4e388 (M.op X0 X0)
               grind)
            | exact superpose b4e388 b4e491
            | exact resolve b4e491 b4e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e491
          have b4e534 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e485 X0 X1 x x
               have i₂ := b4e130 X0 (M.op x x) X1
               grind)
            | exact superpose b4e130 b4e485
            | exact resolve b4e485 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130 b4e485
          have b4e538 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e477 X0 X1
               have i₂ := b4e40 X1 X1 X1
               grind)
            | exact superpose b4e40 b4e477
            | exact resolve b4e477 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e477
          have b4e561 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e534 X0 X1
               have i₂ := b4e522 X0 (M.op X1 X1) X0
               grind)
            | (have i₁ := b4e534 y X1
               have i₂ := b4e522 (M.op y (M.op y y)) (M.op X1 X1) x
               grind)
            | exact superpose b4e522 b4e534
            | exact resolve b4e534 b4e522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e522 b4e534
          have b4e651 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e39 X2 (M.op x X0) (M.op X1 X1) X4
               have i₂ := b4e40 X1 X0 x
               grind)
            | exact superpose b4e40 b4e39
            | exact resolve b4e39 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e745 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X3 (M.op (M.op X2 X2) (M.op X2 X2)) X4
               have i₂ := b4e39 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e751 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 (M.op (M.op X2 X2) (M.op X2 X2))
               have i₂ := b4e39 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b4e39 b4e38
            | exact resolve b4e38 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e790 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e751 X0 X1 X1
               have i₂ := b4e40 X1 X1 X1
               grind)
            | exact superpose b4e40 b4e751
            | exact resolve b4e751 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e751
          have b4e795 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e745 X0 X1 X1 X3 X4
               have i₂ := b4e40 X1 X1 X1
               grind)
            | exact superpose b4e40 b4e745
            | exact resolve b4e745 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e745
          have b4e862 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e651 X0 X1 X2 X4
               have i₂ := b4e44 X1 (M.op X4 X4)
               grind)
            | exact superpose b4e44 b4e651
            | exact resolve b4e651 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e651
          have b4e883 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e790 X0 X1 X2
               have i₂ := b4e538 X1 X2
               grind)
            | exact superpose b4e538 b4e790
            | exact resolve b4e790 b4e538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e790
          have b4e888 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e795 X0 X1 X2 X3 X4
               have i₂ := b4e538 X1 X2
               grind)
            | exact superpose b4e538 b4e795
            | exact resolve b4e795 b4e538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e795
          have b4e929 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) = (M.op (M.op y X1) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e862 X0 X1 X2 X4
               have i₂ := b4e561 X1 X4
               grind)
            | exact superpose b4e561 b4e862
            | exact resolve b4e862 b4e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e561 b4e862
          have b4e938 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e883 X0 X1 X2
               have i₂ := b4e530 X2
               grind)
            | exact superpose b4e530 b4e883
            | exact resolve b4e883 b4e530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e530 b4e883
          have b4e943 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) = (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e888 X0 X1 X2 X3 X4
               have i₂ := b4e538 (M.op X4 X3) X2
               grind)
            | exact superpose b4e538 b4e888
            | exact resolve b4e888 b4e538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e888
          have b4e972 : ∀ X2 : G, (M.op y X2) = (M.op x (M.op (M.op y X2) X2)) := by
            intro X2
            first
            | (have i₁ := b4e938 x x X2
               have i₂ := b4e929 x X2 x X2
               grind)
            | exact superpose b4e929 b4e938
            | exact resolve b4e938 b4e929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e938
          have b4e976 : ∀ X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) = (M.op X3 (M.op (M.op y X2) X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b4e943 x x X2 X3 X4
               have i₂ := b4e929 x X2 x X2
               grind)
            | exact superpose b4e929 b4e943
            | exact resolve b4e943 b4e929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e929 b4e943
          have b4e1436 : (M.op y x) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e972 x
               have i₂ := b4e43 x y
               grind)
            | exact superpose b4e43 b4e972
            | exact resolve b4e972 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e972
          have b4e1463 : y = (M.op x y) := by
            first
            | (have i₁ := b4e1436
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1436
            | exact resolve b4e1436 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1436
          have b4e1512 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e44 X1 (M.op X0 X0)
               have i₂ := b4e40 X0 X0 X0
               grind)
            | exact superpose b4e40 b4e44
            | exact resolve b4e44 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1540 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 X0 X0 (M.op X1 X1) X2
               have i₂ := b4e44 X0 X1
               grind)
            | exact superpose b4e44 b4e33
            | exact resolve b4e33 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e44
          have b4e1597 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1512 X0 X1
               have i₂ := b4e1540 X1 X0 y
               grind)
            | exact superpose b4e1540 b4e1512
            | exact resolve b4e1512 b4e1540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1512 b4e1540
          have b4e1610 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1597 X0 X1
               have i₂ := b4e538 (M.op X1 X1) X0
               grind)
            | exact superpose b4e538 b4e1597
            | exact resolve b4e1597 b4e538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e538 b4e1597
          have b4e1620 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X0) X0)) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1610 X0 X1
               have i₂ := b4e976 X0 X1 X1
               grind)
            | exact superpose b4e976 b4e1610
            | exact resolve b4e1610 b4e976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1610
          have b4e1665 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) = (M.op X2 (M.op y (M.op (M.op x x) (M.op x x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e39 X0 X1 X2 (M.op x x)
               have i₂ := b4e60 (M.op x x) (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b4e60 b4e39
            | exact resolve b4e39 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e60
          have b4e1714 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1665 X0 X1 X2
               have i₂ := b4e388 (M.op x x)
               grind)
            | (have i₁ := b4e1665 X0 X1 X2
               have i₂ := b4e388 (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b4e388 b4e1665
            | exact resolve b4e1665 b4e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1665
          have b4e1734 : ∀ X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X1 X2) (M.op x (M.op x x))) := by
            intro X1 X2
            first
            | (have i₁ := b4e1714 x X1 X2
               have i₂ := b4e40 x (M.op X1 X2) x
               grind)
            | exact superpose b4e40 b4e1714
            | exact resolve b4e1714 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e1714
          have b4e1745 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op (M.op y x) x)) := by
            intro X2
            first
            | (have i₁ := b4e1734 x X2
               have i₂ := b4e976 x X2 x
               grind)
            | exact superpose b4e976 b4e1734
            | exact resolve b4e1734 b4e976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e976 b4e1734
          have b4e1750 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op y X2) x) := by
            intro X2
            first
            | (have i₁ := b4e1745 X2
               have i₂ := b4e1620 x X2
               grind)
            | exact superpose b4e1620 b4e1745
            | exact resolve b4e1745 b4e1620
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1620 b4e1745
          have b4e1751 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b4e1750 X2
               have i₂ := b4e13 X2 x y
               grind)
            | exact superpose b4e13 b4e1750
            | exact resolve b4e1750 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1750
          have b4e1752 : ∀ X2 : G, (M.op X2 (M.op y x)) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b4e1751 X2
               have i₂ := b4e388 x
               grind)
            | (have i₁ := b4e1751 X2
               have i₂ := b4e388 (M.op x x)
               grind)
            | exact superpose b4e388 b4e1751
            | exact resolve b4e1751 b4e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1751
          have b4e1753 : ∀ X2 : G, (M.op X2 y) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b4e1752 X2
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1752
            | exact resolve b4e1752 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1752
          have b4e2256 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b4e388 x
               have i₂ := b4e1753 y
               grind)
            | exact superpose b4e1753 b4e388
            | exact resolve b4e388 b4e1753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e388 b4e1753
          have b4e2259 : y = (M.op y y) := by
            first
            | (have i₁ := b4e2256
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2256
            | exact resolve b4e2256 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2256
          have b4e3895 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e172 y
               have i₂ := b4e2259
               grind)
            | exact superpose b4e2259 b4e172
            | exact resolve b4e172 b4e2259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e172
          have b4e3916 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e3895
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e3895
            | exact resolve b4e3895 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e3895
          have b4e3932 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e3916
               have i₂ := b4e2259
               grind)
            | exact superpose b4e2259 b4e3916
            | exact resolve b4e3916 b4e2259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2259 b4e3916
          have b4e3965 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3932
               grind)
            | exact superpose b4e3932 b4e20
            | exact resolve b4e20 b4e3932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3932
          have b4e3985 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e3965
               have i₂ := b4e1463
               grind)
            | exact superpose b4e1463 b4e3965
            | exact resolve b4e3965 b4e1463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1463 b4e3965
          have b4e3986 : False := by grind
          exact b4e3986
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X1 X1) X3
               have i₂ := b5e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X2) X3 X1
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op x X0)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X3 X3) X1
               have i₂ := b5e13 (M.op X1 X2) X3 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e32 x X1 X2 X3
               have i₂ := b5e37 x X1 X1
               grind)
            | exact superpose b5e37 b5e32
            | exact resolve b5e32 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e37
          have b5e42 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 X1
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X0) X1 x
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e55 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 X1 (M.op x X0)
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e42
            | exact resolve b5e42 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e88 : ∀ X0 : G, (M.op y (σ X0)) = (M.op x (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e35 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e35
            | exact resolve b5e35 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e89 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 (σ X0) X2
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) X1 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e122 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X1 (σ X0) X2 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e33
            | exact resolve b5e33 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e123 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X1 (M.op X0 X0) X2 x
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e33
            | exact resolve b5e33 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e305 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e42 (M.op X2 X2) x
               have i₂ := b5e36 X0 X1 x X2
               grind)
            | exact superpose b5e36 b5e42
            | exact resolve b5e42 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e338 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
            intro X2
            first
            | (have i₁ := b5e305 x x X2
               have i₂ := b5e42 X2 (M.op x x)
               grind)
            | exact superpose b5e42 b5e305
            | exact resolve b5e305 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e305
          have b5e424 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X1 X1) x
               have i₂ := b5e39 X1 X0 x
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e433 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36 X2 X3 (M.op X0 X0) X1
               have i₂ := b5e39 X0 X0 X0
               grind)
            | exact superpose b5e39 b5e36
            | exact resolve b5e36 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e437 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e338 (M.op X0 X0)
               have i₂ := b5e39 X0 X0 X0
               grind)
            | exact superpose b5e39 b5e338
            | exact resolve b5e338 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e452 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33 X1 (M.op X2 (M.op X2 X2)) X3 X4
               have i₂ := b5e39 X2 X1 X0
               grind)
            | exact superpose b5e39 b5e33
            | exact resolve b5e33 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e467 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e452 x x X2 X3 X4
               have i₂ := b5e123 X2 (M.op x x) X3
               grind)
            | exact superpose b5e123 b5e452
            | exact resolve b5e452 b5e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e452
          have b5e475 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e437 X0
               have i₂ := b5e338 X0
               grind)
            | (have i₁ := b5e437 X0
               have i₂ := b5e338 (M.op X0 X0)
               grind)
            | exact superpose b5e338 b5e437
            | exact resolve b5e437 b5e338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e437
          have b5e478 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e433 X0 X1 x x
               have i₂ := b5e123 X0 (M.op x x) X1
               grind)
            | exact superpose b5e123 b5e433
            | exact resolve b5e433 b5e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123 b5e433
          have b5e483 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e424 X0 X1
               have i₂ := b5e39 X1 X1 X1
               grind)
            | exact superpose b5e39 b5e424
            | exact resolve b5e424 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e424
          have b5e504 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e478 X0 X1
               have i₂ := b5e467 X0 (M.op X1 X1) X0
               grind)
            | (have i₁ := b5e478 y X1
               have i₂ := b5e467 (M.op y (M.op y y)) (M.op X1 X1) x
               grind)
            | exact superpose b5e467 b5e478
            | exact resolve b5e478 b5e467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e467 b5e478
          have b5e589 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e38 X2 (M.op x X0) (M.op X1 X1) X4
               have i₂ := b5e39 X1 X0 x
               grind)
            | exact superpose b5e39 b5e38
            | exact resolve b5e38 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e679 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X3 (M.op (M.op X2 X2) (M.op X2 X2)) X4
               have i₂ := b5e38 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e680 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 (M.op (M.op X2 X2) (M.op X2 X2))
               have i₂ := b5e38 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b5e38 b5e35
            | exact resolve b5e35 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e725 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e680 X0 X1 X1
               have i₂ := b5e39 X1 X1 X1
               grind)
            | exact superpose b5e39 b5e680
            | exact resolve b5e680 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e680
          have b5e726 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e679 X0 X1 X1 X3 X4
               have i₂ := b5e39 X1 X1 X1
               grind)
            | exact superpose b5e39 b5e679
            | exact resolve b5e679 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e679
          have b5e790 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e589 X0 X1 X2 X4
               have i₂ := b5e43 X1 (M.op X4 X4)
               grind)
            | exact superpose b5e43 b5e589
            | exact resolve b5e589 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e589
          have b5e814 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e725 X0 X1 X2
               have i₂ := b5e483 X1 X2
               grind)
            | exact superpose b5e483 b5e725
            | exact resolve b5e725 b5e483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e725
          have b5e815 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e726 X0 X1 X2 X3 X4
               have i₂ := b5e483 X1 X2
               grind)
            | exact superpose b5e483 b5e726
            | exact resolve b5e726 b5e483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e726
          have b5e854 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) = (M.op (M.op y X1) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e790 X0 X1 X2 X4
               have i₂ := b5e504 X1 X4
               grind)
            | exact superpose b5e504 b5e790
            | exact resolve b5e790 b5e504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e504 b5e790
          have b5e866 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e814 X0 X1 X2
               have i₂ := b5e475 X2
               grind)
            | exact superpose b5e475 b5e814
            | exact resolve b5e814 b5e475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e475 b5e814
          have b5e867 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) = (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e815 X0 X1 X2 X3 X4
               have i₂ := b5e483 (M.op X4 X3) X2
               grind)
            | exact superpose b5e483 b5e815
            | exact resolve b5e815 b5e483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e815
          have b5e897 : ∀ X2 : G, (M.op y X2) = (M.op x (M.op (M.op y X2) X2)) := by
            intro X2
            first
            | (have i₁ := b5e866 x x X2
               have i₂ := b5e854 x X2 x X2
               grind)
            | exact superpose b5e854 b5e866
            | exact resolve b5e866 b5e854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e866
          have b5e898 : ∀ X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) = (M.op X3 (M.op (M.op y X2) X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e867 x x X2 X3 X4
               have i₂ := b5e854 x X2 x X2
               grind)
            | exact superpose b5e854 b5e867
            | exact resolve b5e867 b5e854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e854 b5e867
          have b5e1138 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op X1 X1)) = (M.op (M.op y (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ (M.op X0 X0)) X1 x
               have i₂ := b5e88 X0
               grind)
            | exact superpose b5e88 b5e13
            | exact resolve b5e13 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1141 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) X2) = (M.op (M.op y (σ X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X1 (σ (M.op X0 X0)) X2 x
               have i₂ := b5e88 X0
               grind)
            | exact superpose b5e88 b5e33
            | exact resolve b5e33 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1310 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e43 X1 (M.op X0 X0)
               have i₂ := b5e39 X0 X0 X0
               grind)
            | exact superpose b5e39 b5e43
            | exact resolve b5e43 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1337 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X0 X0 (M.op X1 X1) X2
               have i₂ := b5e43 X0 X1
               grind)
            | exact superpose b5e43 b5e33
            | exact resolve b5e33 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e1391 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e1310 X0 X1
               have i₂ := b5e1337 X1 X0 y
               grind)
            | exact superpose b5e1337 b5e1310
            | exact resolve b5e1310 b5e1337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1310
          have b5e1403 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1391 X0 X1
               have i₂ := b5e483 (M.op X1 X1) X0
               grind)
            | exact superpose b5e483 b5e1391
            | exact resolve b5e1391 b5e483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e483 b5e1391
          have b5e1412 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X0) X0)) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e1403 X0 X1
               have i₂ := b5e898 X0 X1 X1
               grind)
            | exact superpose b5e898 b5e1403
            | exact resolve b5e1403 b5e898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1403
          have b5e1455 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) = (M.op X2 (M.op y (M.op (M.op x x) (M.op x x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e38 X0 X1 X2 (M.op x x)
               have i₂ := b5e55 (M.op x x) (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b5e55 b5e38
            | exact resolve b5e38 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e55
          have b5e1503 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1455 X0 X1 X2
               have i₂ := b5e338 (M.op x x)
               grind)
            | (have i₁ := b5e1455 X0 X1 X2
               have i₂ := b5e338 (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b5e338 b5e1455
            | exact resolve b5e1455 b5e338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1455
          have b5e1523 : ∀ X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X1 X2) (M.op x (M.op x x))) := by
            intro X1 X2
            first
            | (have i₁ := b5e1503 x X1 X2
               have i₂ := b5e39 x (M.op X1 X2) x
               grind)
            | exact superpose b5e39 b5e1503
            | exact resolve b5e1503 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1503
          have b5e1534 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op (M.op y x) x)) := by
            intro X2
            first
            | (have i₁ := b5e1523 x X2
               have i₂ := b5e898 x X2 x
               grind)
            | exact superpose b5e898 b5e1523
            | exact resolve b5e1523 b5e898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e898 b5e1523
          have b5e1538 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op y X2) x) := by
            intro X2
            first
            | (have i₁ := b5e1534 X2
               have i₂ := b5e1412 x X2
               grind)
            | exact superpose b5e1412 b5e1534
            | exact resolve b5e1534 b5e1412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1412 b5e1534
          have b5e1539 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b5e1538 X2
               have i₂ := b5e13 X2 x y
               grind)
            | exact superpose b5e13 b5e1538
            | exact resolve b5e1538 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1538
          have b5e1540 : ∀ X2 : G, (M.op X2 (M.op y x)) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b5e1539 X2
               have i₂ := b5e338 x
               grind)
            | (have i₁ := b5e1539 X2
               have i₂ := b5e338 (M.op x x)
               grind)
            | exact superpose b5e338 b5e1539
            | exact resolve b5e1539 b5e338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1539
          have b5e1541 : ∀ X2 : G, (M.op X2 y) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b5e1540 X2
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1540
            | exact resolve b5e1540 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1540
          have b5e1675 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b5e338 x
               have i₂ := b5e1541 y
               grind)
            | exact superpose b5e1541 b5e338
            | exact resolve b5e338 b5e1541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e338
          have b5e1678 : y = (M.op y y) := by
            first
            | (have i₁ := b5e1675
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1675
            | exact resolve b5e1675 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1675
          have b5e1948 : ∀ X0 X1 : G, (M.op (M.op y X0) (σ X1)) = (M.op (M.op (M.op y X0) X0) (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e89 X1 (M.op (M.op y X0) X0) x
               have i₂ := b5e897 X0
               grind)
            | exact superpose b5e897 b5e89
            | exact resolve b5e89 b5e897
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e897
          have b5e1950 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X1 X1))) = (M.op (M.op y (σ X0)) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e89 X1 (σ (M.op X0 X0)) x
               have i₂ := b5e88 X0
               grind)
            | exact superpose b5e88 b5e89
            | exact resolve b5e89 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88
          have b5e1971 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ (M.op (M.op x x) y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e89 (M.op x x) X1 X0
               have i₂ := b5e1541 (M.op x x)
               grind)
            | exact superpose b5e1541 b5e89
            | exact resolve b5e89 b5e1541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1973 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ (M.op X0 X0))) = (M.op X2 (σ (M.op (M.op y X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e89 (M.op X0 X0) X2 X1
               have i₂ := b5e43 X0 X0
               grind)
            | exact superpose b5e43 b5e89
            | exact resolve b5e89 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e2114 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ (M.op x (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1971 X0 X1
               have i₂ := b5e13 x y x
               grind)
            | exact superpose b5e13 b5e1971
            | exact resolve b5e1971 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1971
          have b5e2128 : ∀ X0 X1 : G, (M.op (M.op y X0) (σ X1)) = (M.op X0 (σ (M.op (M.op y X1) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1948 X0 X1
               have i₂ := b5e1973 X1 (M.op y X0) X0
               grind)
            | exact superpose b5e1973 b5e1948
            | exact resolve b5e1948 b5e1973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1948
          have b5e2170 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ (M.op y y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2114 X0 X1
               have i₂ := b5e35 y
               grind)
            | exact superpose b5e35 b5e2114
            | exact resolve b5e2114 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2114
          have b5e2199 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2170 X0 X1
               have i₂ := b5e1678
               grind)
            | exact superpose b5e1678 b5e2170
            | exact resolve b5e2170 b5e1678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2170
          have b5e2216 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op (M.op y x) x))) := by
            intro X1
            first
            | (have i₁ := b5e2199 x X1
               have i₂ := b5e1973 x x X1
               grind)
            | exact superpose b5e1973 b5e2199
            | exact resolve b5e2199 b5e1973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2199
          have b5e2227 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op (M.op y X1) (σ x)) := by
            intro X1
            first
            | (have i₁ := b5e2216 X1
               have i₂ := b5e2128 X1 x
               grind)
            | exact superpose b5e2128 b5e2216
            | exact resolve b5e2216 b5e2128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2216
          have b5e2233 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op x x))) := by
            intro X1
            first
            | (have i₁ := b5e2227 X1
               have i₂ := b5e89 x X1 y
               grind)
            | exact superpose b5e89 b5e2227
            | exact resolve b5e2227 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2227
          have b5e2292 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ (M.op (M.op x x) y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e90 (M.op x x) X0
               have i₂ := b5e1541 (M.op x x)
               grind)
            | exact superpose b5e1541 b5e90
            | exact resolve b5e90 b5e1541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1541
          have b5e2304 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e90 y X0
               have i₂ := b5e1678
               grind)
            | exact superpose b5e1678 b5e90
            | exact resolve b5e90 b5e1678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2399 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ (M.op x (M.op y y))) X0) := by
            intro X0
            first
            | (have i₁ := b5e2292 X0
               have i₂ := b5e13 x y x
               grind)
            | exact superpose b5e13 b5e2292
            | exact resolve b5e2292 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2292
          have b5e2442 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ (M.op y y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e2399 X0
               have i₂ := b5e35 y
               grind)
            | exact superpose b5e35 b5e2399
            | exact resolve b5e2399 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e2399
          have b5e2467 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e2442 X0
               have i₂ := b5e1678
               grind)
            | exact superpose b5e1678 b5e2442
            | exact resolve b5e2442 b5e1678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2442
          have b5e2487 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y (σ x)) X0) := by
            intro X0
            first
            | (have i₁ := b5e2467 X0
               have i₂ := b5e1138 x X0
               grind)
            | exact superpose b5e1138 b5e2467
            | exact resolve b5e2467 b5e1138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1138 b5e2467
          have b5e2499 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b5e2487 X0
               have i₂ := b5e122 x y X0
               grind)
            | exact superpose b5e122 b5e2487
            | exact resolve b5e2487 b5e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2487
          have b5e8911 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ (M.op x x)) (σ (M.op x x)))) = (M.op X1 (M.op (σ y) (M.op (σ (M.op x x)) (σ (M.op x x))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e39 (σ (M.op x x)) X1 X0
               have i₂ := b5e2499 (M.op (σ (M.op x x)) (σ (M.op x x)))
               grind)
            | exact superpose b5e2499 b5e39
            | exact resolve b5e39 b5e2499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e8928 : ∀ X0 X1 : G, (M.op (σ y) (σ (M.op X0 X0))) = (M.op (M.op X1 (σ (M.op x x))) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e89 X0 (σ (M.op x x)) X1
               have i₂ := b5e2499 (σ (M.op X0 X0))
               grind)
            | exact superpose b5e2499 b5e89
            | exact resolve b5e89 b5e2499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e8936 : ∀ X0 : G, (M.op (M.op y (σ x)) (σ X0)) = (M.op (σ y) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e8928 X0 x
               have i₂ := b5e1141 x x (σ X0)
               grind)
            | exact superpose b5e1141 b5e8928
            | exact resolve b5e8928 b5e1141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1141 b5e8928
          have b5e8945 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ (M.op x x)) (σ (M.op x x)))) = (M.op X1 (M.op (σ (M.op y y)) (σ (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e8911 X0 X1
               have i₂ := b5e90 y (σ (M.op x x))
               grind)
            | exact superpose b5e90 b5e8911
            | exact resolve b5e8911 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90 b5e8911
          have b5e8994 : ∀ X0 : G, (M.op (σ y) (σ (M.op X0 X0))) = (M.op (σ (M.op x x)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e8936 X0
               have i₂ := b5e122 x y (σ X0)
               grind)
            | exact superpose b5e122 b5e8936
            | exact resolve b5e8936 b5e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122 b5e8936
          have b5e9003 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ (M.op x x)) (σ (M.op x x)))) = (M.op X1 (M.op (M.op y (σ y)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b5e8945 X0 X1
               have i₂ := b5e1950 y x
               grind)
            | exact superpose b5e1950 b5e8945
            | exact resolve b5e8945 b5e1950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1950 b5e8945
          have b5e9045 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (M.op (σ y) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e8994 X0
               have i₂ := b5e2499 (σ X0)
               grind)
            | exact superpose b5e2499 b5e8994
            | exact resolve b5e8994 b5e2499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8994
          have b5e9054 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ (M.op x x)) (σ (M.op x x)))) = (M.op X1 (M.op (σ y) (σ (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e9003 X0 X1
               have i₂ := b5e89 x (σ y) y
               grind)
            | exact superpose b5e89 b5e9003
            | exact resolve b5e9003 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9003
          have b5e9093 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ (M.op x x)) (σ (M.op x x)))) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b5e9054 X0 X1
               have i₂ := b5e9045 x
               grind)
            | exact superpose b5e9045 b5e9054
            | exact resolve b5e9054 b5e9045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9054
          have b5e9124 : ∀ X1 : G, (M.op (M.op y X1) (σ (M.op x x))) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X1
            first
            | (have i₁ := b5e9093 x X1
               have i₂ := b5e1337 X1 (σ (M.op x x)) x
               grind)
            | exact superpose b5e1337 b5e9093
            | exact resolve b5e9093 b5e1337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1337 b5e9093
          have b5e9147 : ∀ X1 : G, (M.op X1 (σ (M.op (M.op y x) x))) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X1
            first
            | (have i₁ := b5e9124 X1
               have i₂ := b5e1973 x y X1
               grind)
            | exact superpose b5e1973 b5e9124
            | exact resolve b5e9124 b5e1973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1973 b5e9124
          have b5e9165 : ∀ X1 : G, (M.op (M.op y X1) (σ x)) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X1
            first
            | (have i₁ := b5e9147 X1
               have i₂ := b5e2128 X1 x
               grind)
            | exact superpose b5e2128 b5e9147
            | exact resolve b5e9147 b5e2128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2128 b5e9147
          have b5e9174 : ∀ X1 : G, (M.op X1 (σ (M.op x x))) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X1
            first
            | (have i₁ := b5e9165 X1
               have i₂ := b5e89 x X1 y
               grind)
            | exact superpose b5e89 b5e9165
            | exact resolve b5e9165 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89 b5e9165
          have b5e9177 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X1
            first
            | (have i₁ := b5e9174 X1
               have i₂ := b5e2233 X1
               grind)
            | exact superpose b5e2233 b5e9174
            | exact resolve b5e9174 b5e2233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2233 b5e9174
          have b5e10621 : (M.op (σ y) (σ (M.op x x))) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
            first
            | (have i₁ := b5e2304 (σ (M.op x x))
               have i₂ := b5e2499 (σ (M.op x x))
               grind)
            | exact superpose b5e2499 b5e2304
            | exact resolve b5e2304 b5e2499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2304 b5e2499
          have b5e10684 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e10621
               have i₂ := b5e9045 x
               grind)
            | exact superpose b5e9045 b5e10621
            | exact resolve b5e10621 b5e9045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9045 b5e10621
          have b5e10715 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e10684
               have i₂ := b5e9177 (σ y)
               grind)
            | exact superpose b5e9177 b5e10684
            | exact resolve b5e10684 b5e9177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9177 b5e10684
          have b5e10726 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e10715
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e10715
            | exact resolve b5e10715 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e10715
          have b5e10735 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e10726
               have i₂ := b5e1678
               grind)
            | exact superpose b5e1678 b5e10726
            | exact resolve b5e10726 b5e1678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1678 b5e10726
          have b5e10740 : False := by grind
          exact b5e10740
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X1 X1) X3
               have i₂ := b7e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X3
               have i₂ := b7e13 X1 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op x X0)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e32 x X1 X2 X3
               have i₂ := b7e37 x X1 X1
               grind)
            | exact superpose b7e37 b7e32
            | exact resolve b7e32 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e47 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e47
          have b7e51 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e52 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e51
            | exact resolve b7e51 b7e19
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
          have b7e62 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e52
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e52 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e63 : (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e64 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e66 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e67 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e22
               grind)
            | exact resolve b7e66 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e69 : x = (M.op x y) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e21
               grind)
            | exact resolve b7e67 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e84 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e13
            | exact resolve b7e13 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e91 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 (σ X0) X2
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e111 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X0 (σ x) X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e112 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 X1 (σ X0) X2 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e33
            | exact resolve b7e33 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e113 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X0 y X1 x
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e33
            | exact resolve b7e33 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e128 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op x x)) X1) := by
            intro X1
            first
            | (have i₁ := b7e111 x X1
               have i₂ := b7e112 x x X1
               grind)
            | exact superpose b7e112 b7e111
            | exact resolve b7e111 b7e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111 b7e112
          have b7e200 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (M.op (σ x) (σ x))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 X1
               have i₂ := b7e37 X0 (σ x) X1
               grind)
            | exact superpose b7e37 b7e35
            | exact resolve b7e35 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e211 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (σ (M.op x x))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e200 X0 X1
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e200
            | exact resolve b7e200 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e200
          have b7e410 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (M.op (σ y) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 (σ x) X1 X0
               have i₂ := b7e35 (σ x)
               grind)
            | exact superpose b7e35 b7e39
            | exact resolve b7e39 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e476 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e410 X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e410
            | exact resolve b7e410 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e410
          have b7e488 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (σ (M.op x x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e476 X0 X1
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e476
            | exact resolve b7e476 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e476
          have b7e1205 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ (M.op x x))) = (M.op X0 (M.op (σ y) (σ (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ (M.op x x)) X1
               have i₂ := b7e128 (σ (M.op x x))
               grind)
            | exact superpose b7e128 b7e13
            | exact resolve b7e13 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1210 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (σ (M.op x x)))) = (M.op (M.op X1 (M.op X0 X0)) (σ (M.op x x))) := by
            intro X0 X1
            first
            | (have i₁ := b7e37 X1 X0 (σ (M.op x x))
               have i₂ := b7e128 (σ (M.op x x))
               grind)
            | exact superpose b7e128 b7e37
            | exact resolve b7e37 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1228 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op x x))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ (M.op x x)) X0 X1
               have i₂ := b7e128 (M.op X0 X0)
               grind)
            | exact superpose b7e128 b7e13
            | exact resolve b7e13 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e1238 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e1228 X0 x
               have i₂ := b7e211 x X0
               grind)
            | exact superpose b7e211 b7e1228
            | exact resolve b7e1228 b7e211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e211 b7e1228
          have b7e1244 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ (M.op x x)))) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e1210 X0 x
               have i₂ := b7e488 x (M.op X0 X0)
               grind)
            | exact superpose b7e488 b7e1210
            | exact resolve b7e1210 b7e488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1210
          have b7e1247 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b7e1205 X0 x
               have i₂ := b7e488 x X0
               grind)
            | exact superpose b7e488 b7e1205
            | exact resolve b7e1205 b7e488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e488 b7e1205
          have b7e1257 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ (M.op x x)))) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b7e1244 X0
               have i₂ := b7e91 y X0 X0
               grind)
            | exact superpose b7e91 b7e1244
            | exact resolve b7e1244 b7e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1244
          have b7e1266 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b7e1257 X0
               have i₂ := b7e1247 X0
               grind)
            | exact superpose b7e1247 b7e1257
            | exact resolve b7e1257 b7e1247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1247 b7e1257
          have b7e1349 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (σ (M.op X1 X1))) = (M.op X3 (σ (M.op (M.op X0 (M.op X1 X1)) X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e91 (M.op X1 X1) X3 X2
               have i₂ := b7e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b7e13 b7e91
            | exact resolve b7e91 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e1473 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X3) (σ (M.op X1 X1))) = (M.op X3 (σ (M.op X1 (M.op X1 X1)))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e1349 x X1 X2 X3
               have i₂ := b7e37 x X1 X1
               grind)
            | exact superpose b7e37 b7e1349
            | exact resolve b7e1349 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37 b7e1349
          have b7e1579 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (σ y))) = (M.op (M.op X0 X1) (M.op (σ y) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 (σ y) X1 X0
               have i₂ := b7e1238 (σ y)
               grind)
            | exact superpose b7e1238 b7e39
            | exact resolve b7e39 b7e1238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e1238
          have b7e1594 : ∀ X0 X1 : G, (M.op X1 (σ (M.op y y))) = (M.op (M.op X0 X1) (σ (M.op y y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1579 X0 X1
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e1579
            | exact resolve b7e1579 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1579
          have b7e1607 : ∀ X1 : G, (M.op X1 (σ (M.op y y))) = (M.op X1 (σ (M.op y (M.op y y)))) := by
            intro X1
            first
            | (have i₁ := b7e1594 x X1
               have i₂ := b7e1473 y x X1
               grind)
            | exact superpose b7e1473 b7e1594
            | exact resolve b7e1594 b7e1473
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1473 b7e1594
          have b7e1614 : ∀ X1 : G, (M.op X1 (σ (M.op y y))) = (M.op X1 (σ (M.op x y))) := by
            intro X1
            first
            | (have i₁ := b7e1607 X1
               have i₂ := b7e84 y
               grind)
            | exact superpose b7e84 b7e1607
            | exact resolve b7e1607 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84 b7e1607
          have b7e1620 : ∀ X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ (M.op y y))) := by
            intro X1
            first
            | (have i₁ := b7e1614 X1
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e1614
            | exact resolve b7e1614 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e1614
          have b7e1622 : ∀ X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
            intro X1
            first
            | (have i₁ := b7e1620 X1
               have i₂ := b7e1266 X1
               grind)
            | exact superpose b7e1266 b7e1620
            | exact resolve b7e1620 b7e1266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1266 b7e1620
          have b7e1887 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e1622 (σ y)
               grind)
            | exact superpose b7e1622 b7e24
            | exact resolve b7e24 b7e1622
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1622
          have b7e1895 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e1887
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e1887
            | exact resolve b7e1887 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e1887
          have b7e2312 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e1895
               grind)
            | exact superpose b7e1895 b7e14
            | exact resolve b7e14 b7e1895
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1895
          have b7e2331 : y = (M.op y y) := by
            first
            | (have i₁ := b7e2312
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e2312
            | exact resolve b7e2312 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2312
          have b7e2630 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e113 y X0
               have i₂ := b7e2331
               grind)
            | exact superpose b7e2331 b7e113
            | exact resolve b7e113 b7e2331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113
          have b7e2747 : x = (M.op y y) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e2630 y
               grind)
            | exact superpose b7e2630 b7e69
            | exact resolve b7e69 b7e2630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e2630
          have b7e2801 : x = y := by
            first
            | (have i₁ := b7e2747
               have i₂ := b7e2331
               grind)
            | exact superpose b7e2331 b7e2747
            | exact resolve b7e2747 b7e2331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2331 b7e2747
          have b7e2821 : False := by grind
          exact b7e2821
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
          have b8e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e1250 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e61 x y
               grind)
            | exact superpose b8e61 b8e20
            | (have j1 := b8e61 x y
               grind)
            | exact resolve b8e20 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e1291 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1250
               have r₂ := b8e24
               grind)
            | exact resolve b8e1250 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1250
          have b8e1304 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1291
               have r₂ := b8e23
               grind)
            | exact resolve b8e1291 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1291
          have b8e1311 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1304
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1304
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1304
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1304
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1304 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1304
          have b8e1312 : y = (M.op y x) ∨ x = y := by grind
          clear b8e1311
          have b8e1313 : x = y := by
            first
            | (have r₁ := b8e1312
               have r₂ := b8e22
               grind)
            | exact resolve b8e1312 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1312
          have b8e1314 : False := by grind
          exact b8e1314

/-- `Equation4490`: `x ◇ (y ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pxy_Equation4490 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4490 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4490.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X1 X1) X3
               have i₂ := b4e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X2 X2) X3 X1
               have i₂ := b4e13 X1 X2 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 (M.op x X0)
               have i₂ := b4e13 X0 X1 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
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
          have b4e38 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
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
          have b4e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X3 X3) X1
               have i₂ := b4e13 (M.op X1 X2) X3 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e32 x X1 X2 X3
               have i₂ := b4e36 x X1 X1
               grind)
            | exact superpose b4e36 b4e32
            | exact resolve b4e32 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e36
          have b4e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 X0) X1 x
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 X1 (M.op x X0)
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e43
            | exact resolve b4e43 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 X1 (M.op X0 X0) X2 x
               have i₂ := b4e38 X0
               grind)
            | exact superpose b4e38 b4e33
            | exact resolve b4e33 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e173 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e37 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e37
            | exact resolve b4e37 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e353 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e43 (M.op X2 X2) x
               have i₂ := b4e35 X0 X1 x X2
               grind)
            | exact superpose b4e35 b4e43
            | exact resolve b4e43 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e388 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
            intro X2
            first
            | (have i₁ := b4e353 x x X2
               have i₂ := b4e43 X2 (M.op x x)
               grind)
            | exact superpose b4e43 b4e353
            | exact resolve b4e353 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e353
          have b4e478 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X1 X1) x
               have i₂ := b4e40 X1 X0 x
               grind)
            | exact superpose b4e40 b4e13
            | exact resolve b4e13 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e35 X2 X3 (M.op X0 X0) X1
               have i₂ := b4e40 X0 X0 X0
               grind)
            | exact superpose b4e40 b4e35
            | exact resolve b4e35 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e492 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e388 (M.op X0 X0)
               have i₂ := b4e40 X0 X0 X0
               grind)
            | exact superpose b4e40 b4e388
            | exact resolve b4e388 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e508 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e33 X1 (M.op X2 (M.op X2 X2)) X3 X4
               have i₂ := b4e40 X2 X1 X0
               grind)
            | exact superpose b4e40 b4e33
            | exact resolve b4e33 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e524 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
            intro X2 X3 X4
            first
            | (have i₁ := b4e508 x x X2 X3 X4
               have i₂ := b4e133 X2 (M.op x x) X3
               grind)
            | exact superpose b4e133 b4e508
            | exact resolve b4e508 b4e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e508
          have b4e533 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b4e492 X0
               have i₂ := b4e388 X0
               grind)
            | (have i₁ := b4e492 X0
               have i₂ := b4e388 (M.op X0 X0)
               grind)
            | exact superpose b4e388 b4e492
            | exact resolve b4e492 b4e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e492
          have b4e537 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 X0 X1 x x
               have i₂ := b4e133 X0 (M.op x x) X1
               grind)
            | exact superpose b4e133 b4e486
            | exact resolve b4e486 b4e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133 b4e486
          have b4e541 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e478 X0 X1
               have i₂ := b4e40 X1 X1 X1
               grind)
            | exact superpose b4e40 b4e478
            | exact resolve b4e478 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e478
          have b4e564 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e537 X0 X1
               have i₂ := b4e524 X0 (M.op X1 X1) X0
               grind)
            | (have i₁ := b4e537 y X1
               have i₂ := b4e524 (M.op y (M.op y y)) (M.op X1 X1) x
               grind)
            | exact superpose b4e524 b4e537
            | exact resolve b4e537 b4e524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e524 b4e537
          have b4e654 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e39 X2 (M.op x X0) (M.op X1 X1) X4
               have i₂ := b4e40 X1 X0 x
               grind)
            | exact superpose b4e40 b4e39
            | exact resolve b4e39 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e748 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X3 (M.op (M.op X2 X2) (M.op X2 X2)) X4
               have i₂ := b4e39 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e754 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 (M.op (M.op X2 X2) (M.op X2 X2))
               have i₂ := b4e39 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b4e39 b4e38
            | exact resolve b4e38 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e793 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e754 X0 X1 X1
               have i₂ := b4e40 X1 X1 X1
               grind)
            | exact superpose b4e40 b4e754
            | exact resolve b4e754 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e754
          have b4e798 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e748 X0 X1 X1 X3 X4
               have i₂ := b4e40 X1 X1 X1
               grind)
            | exact superpose b4e40 b4e748
            | exact resolve b4e748 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e748
          have b4e865 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e654 X0 X1 X2 X4
               have i₂ := b4e44 X1 (M.op X4 X4)
               grind)
            | exact superpose b4e44 b4e654
            | exact resolve b4e654 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e654
          have b4e886 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e793 X0 X1 X2
               have i₂ := b4e541 X1 X2
               grind)
            | exact superpose b4e541 b4e793
            | exact resolve b4e793 b4e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e793
          have b4e891 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e798 X0 X1 X2 X3 X4
               have i₂ := b4e541 X1 X2
               grind)
            | exact superpose b4e541 b4e798
            | exact resolve b4e798 b4e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e798
          have b4e931 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) = (M.op (M.op y X1) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e865 X0 X1 X2 X4
               have i₂ := b4e564 X1 X4
               grind)
            | exact superpose b4e564 b4e865
            | exact resolve b4e865 b4e564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e564 b4e865
          have b4e941 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e886 X0 X1 X2
               have i₂ := b4e533 X2
               grind)
            | exact superpose b4e533 b4e886
            | exact resolve b4e886 b4e533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533 b4e886
          have b4e946 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) = (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e891 X0 X1 X2 X3 X4
               have i₂ := b4e541 (M.op X4 X3) X2
               grind)
            | exact superpose b4e541 b4e891
            | exact resolve b4e891 b4e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e891
          have b4e975 : ∀ X2 : G, (M.op y X2) = (M.op x (M.op (M.op y X2) X2)) := by
            intro X2
            first
            | (have i₁ := b4e941 x x X2
               have i₂ := b4e931 x X2 x X2
               grind)
            | exact superpose b4e931 b4e941
            | exact resolve b4e941 b4e931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e941
          have b4e979 : ∀ X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) = (M.op X3 (M.op (M.op y X2) X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b4e946 x x X2 X3 X4
               have i₂ := b4e931 x X2 x X2
               grind)
            | exact superpose b4e931 b4e946
            | exact resolve b4e946 b4e931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e931 b4e946
          have b4e1422 : (M.op y x) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e975 x
               have i₂ := b4e43 x y
               grind)
            | exact superpose b4e43 b4e975
            | exact resolve b4e975 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e975
          have b4e1452 : y = (M.op x y) := by
            first
            | (have i₁ := b4e1422
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1422
            | exact resolve b4e1422 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1422
          have b4e1490 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e44 X1 (M.op X0 X0)
               have i₂ := b4e40 X0 X0 X0
               grind)
            | exact superpose b4e40 b4e44
            | exact resolve b4e44 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1520 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 X0 X0 (M.op X1 X1) X2
               have i₂ := b4e44 X0 X1
               grind)
            | exact superpose b4e44 b4e33
            | exact resolve b4e33 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e44
          have b4e1580 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1490 X0 X1
               have i₂ := b4e1520 X1 X0 y
               grind)
            | exact superpose b4e1520 b4e1490
            | exact resolve b4e1490 b4e1520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1490 b4e1520
          have b4e1592 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1580 X0 X1
               have i₂ := b4e541 (M.op X1 X1) X0
               grind)
            | exact superpose b4e541 b4e1580
            | exact resolve b4e1580 b4e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e541 b4e1580
          have b4e1601 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X0) X0)) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1592 X0 X1
               have i₂ := b4e979 X0 X1 X1
               grind)
            | exact superpose b4e979 b4e1592
            | exact resolve b4e1592 b4e979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1592
          have b4e2088 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) = (M.op X2 (M.op y (M.op (M.op x x) (M.op x x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e39 X0 X1 X2 (M.op x x)
               have i₂ := b4e63 (M.op x x) (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b4e63 b4e39
            | exact resolve b4e39 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e63
          have b4e2148 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2088 X0 X1 X2
               have i₂ := b4e388 (M.op x x)
               grind)
            | (have i₁ := b4e2088 X0 X1 X2
               have i₂ := b4e388 (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b4e388 b4e2088
            | exact resolve b4e2088 b4e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2088
          have b4e2173 : ∀ X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X1 X2) (M.op x (M.op x x))) := by
            intro X1 X2
            first
            | (have i₁ := b4e2148 x X1 X2
               have i₂ := b4e40 x (M.op X1 X2) x
               grind)
            | exact superpose b4e40 b4e2148
            | exact resolve b4e2148 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e2148
          have b4e2186 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op (M.op y x) x)) := by
            intro X2
            first
            | (have i₁ := b4e2173 x X2
               have i₂ := b4e979 x X2 x
               grind)
            | exact superpose b4e979 b4e2173
            | exact resolve b4e2173 b4e979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e979 b4e2173
          have b4e2191 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op y X2) x) := by
            intro X2
            first
            | (have i₁ := b4e2186 X2
               have i₂ := b4e1601 x X2
               grind)
            | exact superpose b4e1601 b4e2186
            | exact resolve b4e2186 b4e1601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1601 b4e2186
          have b4e2192 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b4e2191 X2
               have i₂ := b4e13 X2 x y
               grind)
            | exact superpose b4e13 b4e2191
            | exact resolve b4e2191 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2191
          have b4e2193 : ∀ X2 : G, (M.op X2 (M.op y x)) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b4e2192 X2
               have i₂ := b4e388 x
               grind)
            | (have i₁ := b4e2192 X2
               have i₂ := b4e388 (M.op x x)
               grind)
            | exact superpose b4e388 b4e2192
            | exact resolve b4e2192 b4e388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2192
          have b4e2194 : ∀ X2 : G, (M.op X2 y) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b4e2193 X2
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2193
            | exact resolve b4e2193 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2193
          have b4e2492 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b4e388 x
               have i₂ := b4e2194 y
               grind)
            | exact superpose b4e2194 b4e388
            | exact resolve b4e388 b4e2194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e388 b4e2194
          have b4e2495 : y = (M.op y y) := by
            first
            | (have i₁ := b4e2492
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2492
            | exact resolve b4e2492 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2492
          have b4e3881 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e173 y
               have i₂ := b4e2495
               grind)
            | exact superpose b4e2495 b4e173
            | exact resolve b4e173 b4e2495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173
          have b4e3901 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e3881
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e3881
            | exact resolve b4e3881 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e3881
          have b4e3917 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e3901
               have i₂ := b4e2495
               grind)
            | exact superpose b4e2495 b4e3901
            | exact resolve b4e3901 b4e2495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2495 b4e3901
          have b4e3950 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3917
               grind)
            | exact superpose b4e3917 b4e20
            | exact resolve b4e20 b4e3917
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3917
          have b4e3969 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e3950
               have i₂ := b4e1452
               grind)
            | exact superpose b4e1452 b4e3950
            | exact resolve b4e3950 b4e1452
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1452 b4e3950
          have b4e3970 : False := by grind
          exact b4e3970
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X1 X1) X3
               have i₂ := b5e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X2) X3 X1
               have i₂ := b5e13 X1 X2 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op x X0)
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op X3 X3) X1
               have i₂ := b5e13 (M.op X1 X2) X3 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e32 x X1 X2 X3
               have i₂ := b5e37 x X1 X1
               grind)
            | exact superpose b5e37 b5e32
            | exact resolve b5e32 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e42 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 X1
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X0) X1 x
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 (M.op x x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 X1 (M.op x X0)
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e42
            | exact resolve b5e42 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 : G, (M.op y (σ X0)) = (M.op x (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e35 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e35
            | exact resolve b5e35 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e91 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 (σ X0) X2
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e92 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) X1 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e125 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X1 (M.op X0 X0) X2 x
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e33
            | exact resolve b5e33 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e178 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (M.op X2 (σ (M.op X0 X0))) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37 X2 (σ X0) X1
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e37
            | exact resolve b5e37 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e308 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e42 (M.op X2 X2) x
               have i₂ := b5e36 X0 X1 x X2
               grind)
            | exact superpose b5e36 b5e42
            | exact resolve b5e42 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e342 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
            intro X2
            first
            | (have i₁ := b5e308 x x X2
               have i₂ := b5e42 X2 (M.op x x)
               grind)
            | exact superpose b5e42 b5e308
            | exact resolve b5e308 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e308
          have b5e364 : ∀ X0 : G, (M.op y (σ X0)) = (M.op y (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e342 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e342
            | exact resolve b5e342 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e429 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X1 X1) x
               have i₂ := b5e39 X1 X0 x
               grind)
            | exact superpose b5e39 b5e13
            | exact resolve b5e13 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e438 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36 X2 X3 (M.op X0 X0) X1
               have i₂ := b5e39 X0 X0 X0
               grind)
            | exact superpose b5e39 b5e36
            | exact resolve b5e36 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e442 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e342 (M.op X0 X0)
               have i₂ := b5e39 X0 X0 X0
               grind)
            | exact superpose b5e39 b5e342
            | exact resolve b5e342 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e457 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33 X1 (M.op X2 (M.op X2 X2)) X3 X4
               have i₂ := b5e39 X2 X1 X0
               grind)
            | exact superpose b5e39 b5e33
            | exact resolve b5e33 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e473 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e457 x x X2 X3 X4
               have i₂ := b5e125 X2 (M.op x x) X3
               grind)
            | exact superpose b5e125 b5e457
            | exact resolve b5e457 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e457
          have b5e482 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e442 X0
               have i₂ := b5e342 X0
               grind)
            | (have i₁ := b5e442 X0
               have i₂ := b5e342 (M.op X0 X0)
               grind)
            | exact superpose b5e342 b5e442
            | exact resolve b5e442 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e442
          have b5e485 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e438 X0 X1 x x
               have i₂ := b5e125 X0 (M.op x x) X1
               grind)
            | exact superpose b5e125 b5e438
            | exact resolve b5e438 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125 b5e438
          have b5e490 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e429 X0 X1
               have i₂ := b5e39 X1 X1 X1
               grind)
            | exact superpose b5e39 b5e429
            | exact resolve b5e429 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e429
          have b5e511 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e485 X0 X1
               have i₂ := b5e473 X0 (M.op X1 X1) X0
               grind)
            | (have i₁ := b5e485 y X1
               have i₂ := b5e473 (M.op y (M.op y y)) (M.op X1 X1) x
               grind)
            | exact superpose b5e473 b5e485
            | exact resolve b5e485 b5e473
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e473 b5e485
          have b5e596 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e38 X2 (M.op x X0) (M.op X1 X1) X4
               have i₂ := b5e39 X1 X0 x
               grind)
            | exact superpose b5e39 b5e38
            | exact resolve b5e38 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e686 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X3 (M.op (M.op X2 X2) (M.op X2 X2)) X4
               have i₂ := b5e38 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e687 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 (M.op (M.op X2 X2) (M.op X2 X2))
               have i₂ := b5e38 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
               grind)
            | exact superpose b5e38 b5e35
            | exact resolve b5e35 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e732 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e687 X0 X1 X1
               have i₂ := b5e39 X1 X1 X1
               grind)
            | exact superpose b5e39 b5e687
            | exact resolve b5e687 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e687
          have b5e733 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e686 X0 X1 X1 X3 X4
               have i₂ := b5e39 X1 X1 X1
               grind)
            | exact superpose b5e39 b5e686
            | exact resolve b5e686 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e686
          have b5e797 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e596 X0 X1 X2 X4
               have i₂ := b5e43 X1 (M.op X4 X4)
               grind)
            | exact superpose b5e43 b5e596
            | exact resolve b5e596 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e596
          have b5e821 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e732 X0 X1 X2
               have i₂ := b5e490 X1 X2
               grind)
            | exact superpose b5e490 b5e732
            | exact resolve b5e732 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e732
          have b5e822 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e733 X0 X1 X2 X3 X4
               have i₂ := b5e490 X1 X2
               grind)
            | exact superpose b5e490 b5e733
            | exact resolve b5e733 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e733
          have b5e861 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) = (M.op (M.op y X1) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e797 X0 X1 X2 X4
               have i₂ := b5e511 X1 X4
               grind)
            | exact superpose b5e511 b5e797
            | exact resolve b5e797 b5e511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e511 b5e797
          have b5e874 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e821 X0 X1 X2
               have i₂ := b5e482 X2
               grind)
            | exact superpose b5e482 b5e821
            | exact resolve b5e821 b5e482
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e482 b5e821
          have b5e875 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) = (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e822 X0 X1 X2 X3 X4
               have i₂ := b5e490 (M.op X4 X3) X2
               grind)
            | exact superpose b5e490 b5e822
            | exact resolve b5e822 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e822
          have b5e906 : ∀ X2 : G, (M.op y X2) = (M.op x (M.op (M.op y X2) X2)) := by
            intro X2
            first
            | (have i₁ := b5e874 x x X2
               have i₂ := b5e861 x X2 x X2
               grind)
            | exact superpose b5e861 b5e874
            | exact resolve b5e874 b5e861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e874
          have b5e907 : ∀ X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X2 (M.op X2 X2))) = (M.op X3 (M.op (M.op y X2) X2)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e875 x x X2 X3 X4
               have i₂ := b5e861 x X2 x X2
               grind)
            | exact superpose b5e861 b5e875
            | exact resolve b5e875 b5e861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e861 b5e875
          have b5e1245 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op X1 X1)) = (M.op (M.op y (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ (M.op X0 X0)) X1 x
               have i₂ := b5e90 X0
               grind)
            | exact superpose b5e90 b5e13
            | exact resolve b5e13 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1353 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e43 X1 (M.op X0 X0)
               have i₂ := b5e39 X0 X0 X0
               grind)
            | exact superpose b5e39 b5e43
            | exact resolve b5e43 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1374 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e39 X1 X0 X0
               have i₂ := b5e43 X0 X1
               grind)
            | exact superpose b5e43 b5e39
            | exact resolve b5e39 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1380 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 X0 X0 (M.op X1 X1) X2
               have i₂ := b5e43 X0 X1
               grind)
            | exact superpose b5e43 b5e33
            | exact resolve b5e33 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e1435 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e1353 X0 X1
               have i₂ := b5e1380 X1 X0 y
               grind)
            | exact superpose b5e1380 b5e1353
            | exact resolve b5e1353 b5e1380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1353 b5e1380
          have b5e1447 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1435 X0 X1
               have i₂ := b5e490 (M.op X1 X1) X0
               grind)
            | exact superpose b5e490 b5e1435
            | exact resolve b5e1435 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e490 b5e1435
          have b5e1456 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X0) X0)) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e1447 X0 X1
               have i₂ := b5e907 X0 X1 X1
               grind)
            | exact superpose b5e907 b5e1447
            | exact resolve b5e1447 b5e907
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1447
          have b5e1501 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) = (M.op X2 (M.op y (M.op (M.op x x) (M.op x x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e38 X0 X1 X2 (M.op x x)
               have i₂ := b5e57 (M.op x x) (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b5e57 b5e38
            | exact resolve b5e38 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e57
          have b5e1549 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X0 (M.op X1 X2)) (M.op x x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1501 X0 X1 X2
               have i₂ := b5e342 (M.op x x)
               grind)
            | (have i₁ := b5e1501 X0 X1 X2
               have i₂ := b5e342 (M.op (M.op x x) (M.op x x))
               grind)
            | exact superpose b5e342 b5e1501
            | exact resolve b5e1501 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1501
          have b5e1570 : ∀ X1 X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op X1 X2) (M.op x (M.op x x))) := by
            intro X1 X2
            first
            | (have i₁ := b5e1549 x X1 X2
               have i₂ := b5e39 x (M.op X1 X2) x
               grind)
            | exact superpose b5e39 b5e1549
            | exact resolve b5e1549 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1549
          have b5e1581 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op (M.op y x) x)) := by
            intro X2
            first
            | (have i₁ := b5e1570 x X2
               have i₂ := b5e907 x X2 x
               grind)
            | exact superpose b5e907 b5e1570
            | exact resolve b5e1570 b5e907
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e907 b5e1570
          have b5e1585 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op (M.op y X2) x) := by
            intro X2
            first
            | (have i₁ := b5e1581 X2
               have i₂ := b5e1456 x X2
               grind)
            | exact superpose b5e1456 b5e1581
            | exact resolve b5e1581 b5e1456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1456 b5e1581
          have b5e1586 : ∀ X2 : G, (M.op X2 (M.op y (M.op x x))) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b5e1585 X2
               have i₂ := b5e13 X2 x y
               grind)
            | exact superpose b5e13 b5e1585
            | exact resolve b5e1585 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1585
          have b5e1587 : ∀ X2 : G, (M.op X2 (M.op y x)) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b5e1586 X2
               have i₂ := b5e342 x
               grind)
            | (have i₁ := b5e1586 X2
               have i₂ := b5e342 (M.op x x)
               grind)
            | exact superpose b5e342 b5e1586
            | exact resolve b5e1586 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1586
          have b5e1588 : ∀ X2 : G, (M.op X2 y) = (M.op X2 (M.op x x)) := by
            intro X2
            first
            | (have i₁ := b5e1587 X2
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1587
            | exact resolve b5e1587 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1587
          have b5e1698 : (M.op y (σ (M.op x x))) = (M.op x (σ (M.op (M.op x x) y))) := by
            first
            | (have i₁ := b5e90 (M.op x x)
               have i₂ := b5e1588 (M.op x x)
               grind)
            | exact superpose b5e1588 b5e90
            | exact resolve b5e90 b5e1588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1726 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b5e342 x
               have i₂ := b5e1588 y
               grind)
            | exact superpose b5e1588 b5e342
            | exact resolve b5e342 b5e1588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1729 : y = (M.op y y) := by
            first
            | (have i₁ := b5e1726
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1726
            | exact resolve b5e1726 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1726
          have b5e1756 : (M.op y (σ (M.op x x))) = (M.op x (σ (M.op x (M.op y y)))) := by
            first
            | (have i₁ := b5e1698
               have i₂ := b5e13 x y x
               grind)
            | exact superpose b5e13 b5e1698
            | exact resolve b5e1698 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1698
          have b5e1810 : (M.op y (σ (M.op x x))) = (M.op x (σ (M.op y y))) := by
            first
            | (have i₁ := b5e1756
               have i₂ := b5e35 y
               grind)
            | exact superpose b5e35 b5e1756
            | exact resolve b5e1756 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1756
          have b5e1856 : (M.op y (σ (M.op x x))) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e1810
               have i₂ := b5e90 y
               grind)
            | exact superpose b5e90 b5e1810
            | exact resolve b5e1810 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90 b5e1810
          have b5e1892 : (M.op y (σ y)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e1856
               have i₂ := b5e364 x
               grind)
            | exact superpose b5e364 b5e1856
            | exact resolve b5e1856 b5e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e364 b5e1856
          have b5e2006 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e91 X1 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e91
            | exact resolve b5e91 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2011 : ∀ X0 X1 : G, (M.op (M.op y X0) (σ X1)) = (M.op (M.op (M.op y X0) X0) (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e91 X1 (M.op (M.op y X0) X0) x
               have i₂ := b5e906 X0
               grind)
            | exact superpose b5e906 b5e91
            | exact resolve b5e91 b5e906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e906
          have b5e2034 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ (M.op (M.op x x) y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e91 (M.op x x) X1 X0
               have i₂ := b5e1588 (M.op x x)
               grind)
            | exact superpose b5e1588 b5e91
            | exact resolve b5e91 b5e1588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2036 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ (M.op X0 X0))) = (M.op X2 (σ (M.op (M.op y X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e91 (M.op X0 X0) X2 X1
               have i₂ := b5e43 X0 X0
               grind)
            | exact superpose b5e43 b5e91
            | exact resolve b5e91 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e2118 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op X0 (σ (M.op X1 X1))) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 (M.op X1 X1)
               have i₂ := b5e91 X1 (σ (M.op X1 X1)) X0
               grind)
            | exact superpose b5e91 b5e30
            | exact resolve b5e30 b5e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e2124 : ∀ X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (σ X1) (M.op (σ X1) (σ X1))) := by
            intro X1
            first
            | (have i₁ := b5e2118 x X1
               have i₂ := b5e178 X1 (σ X1) x
               grind)
            | exact superpose b5e178 b5e2118
            | exact resolve b5e2118 b5e178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e178 b5e2118
          have b5e2180 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ (M.op x (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2034 X0 X1
               have i₂ := b5e13 x y x
               grind)
            | exact superpose b5e13 b5e2034
            | exact resolve b5e2034 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2034
          have b5e2194 : ∀ X0 X1 : G, (M.op (M.op y X0) (σ X1)) = (M.op X0 (σ (M.op (M.op y X1) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2011 X0 X1
               have i₂ := b5e2036 X1 (M.op y X0) X0
               grind)
            | exact superpose b5e2036 b5e2011
            | exact resolve b5e2011 b5e2036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2011
          have b5e2206 : ∀ X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (σ (M.op X1 X1)) (σ X1)) := by
            intro X1
            first
            | (have i₁ := b5e2124 X1
               have i₂ := b5e92 X1 (σ X1)
               grind)
            | exact superpose b5e92 b5e2124
            | exact resolve b5e2124 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2124
          have b5e2237 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ (M.op y y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e2180 X0 X1
               have i₂ := b5e35 y
               grind)
            | exact superpose b5e35 b5e2180
            | exact resolve b5e2180 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2180
          have b5e2250 : ∀ X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (σ X1) (σ (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b5e2206 X1
               have i₂ := b5e2006 X1 X1
               grind)
            | exact superpose b5e2006 b5e2206
            | exact resolve b5e2206 b5e2006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2006 b5e2206
          have b5e2269 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x x))) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2237 X0 X1
               have i₂ := b5e1729
               grind)
            | exact superpose b5e1729 b5e2237
            | exact resolve b5e2237 b5e1729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2237
          have b5e2276 : ∀ X1 : G, (σ (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op (σ X1) (σ (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b5e2250 X1
               have i₂ := b5e39 X1 X1 X1
               grind)
            | exact superpose b5e39 b5e2250
            | exact resolve b5e2250 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e2250
          have b5e2288 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op (M.op y x) x))) := by
            intro X1
            first
            | (have i₁ := b5e2269 x X1
               have i₂ := b5e2036 x x X1
               grind)
            | exact superpose b5e2036 b5e2269
            | exact resolve b5e2269 b5e2036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2036 b5e2269
          have b5e2293 : ∀ X1 : G, (σ (M.op (M.op y X1) X1)) = (M.op (σ X1) (σ (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b5e2276 X1
               have i₂ := b5e1374 X1 X1
               grind)
            | exact superpose b5e1374 b5e2276
            | exact resolve b5e2276 b5e1374
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1374 b5e2276
          have b5e2300 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op (M.op y X1) (σ x)) := by
            intro X1
            first
            | (have i₁ := b5e2288 X1
               have i₂ := b5e2194 X1 x
               grind)
            | exact superpose b5e2194 b5e2288
            | exact resolve b5e2288 b5e2194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2194 b5e2288
          have b5e2307 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (M.op x x))) := by
            intro X1
            first
            | (have i₁ := b5e2300 X1
               have i₂ := b5e91 x X1 y
               grind)
            | exact superpose b5e91 b5e2300
            | exact resolve b5e2300 b5e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2300
          have b5e2374 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ (M.op (M.op x x) y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e92 (M.op x x) X0
               have i₂ := b5e1588 (M.op x x)
               grind)
            | exact superpose b5e1588 b5e92
            | exact resolve b5e92 b5e1588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92 b5e1588
          have b5e2483 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ (M.op x (M.op y y))) X0) := by
            intro X0
            first
            | (have i₁ := b5e2374 X0
               have i₂ := b5e13 x y x
               grind)
            | exact superpose b5e13 b5e2374
            | exact resolve b5e2374 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2374
          have b5e2526 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ (M.op y y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e2483 X0
               have i₂ := b5e35 y
               grind)
            | exact superpose b5e35 b5e2483
            | exact resolve b5e2483 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e2483
          have b5e2551 : ∀ X0 : G, (M.op (σ (M.op x x)) (M.op X0 X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e2526 X0
               have i₂ := b5e1729
               grind)
            | exact superpose b5e1729 b5e2526
            | exact resolve b5e2526 b5e1729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2526
          have b5e2571 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y (σ x)) X0) := by
            intro X0
            first
            | (have i₁ := b5e2551 X0
               have i₂ := b5e1245 x X0
               grind)
            | exact superpose b5e1245 b5e2551
            | exact resolve b5e2551 b5e1245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1245 b5e2551
          have b5e2583 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e2571 X0
               have i₂ := b5e1892
               grind)
            | exact superpose b5e1892 b5e2571
            | exact resolve b5e2571 b5e1892
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1892 b5e2571
          have b5e8973 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (M.op (σ y) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e91 X0 (σ y) y
               have i₂ := b5e2583 (σ X0)
               grind)
            | exact superpose b5e2583 b5e91
            | exact resolve b5e91 b5e2583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e9049 : (M.op (σ y) (σ (M.op x x))) = (M.op (M.op y (σ y)) (σ y)) := by
            first
            | (have i₁ := b5e2307 (M.op y (σ y))
               have i₂ := b5e2583 (σ (M.op x x))
               grind)
            | exact superpose b5e2583 b5e2307
            | exact resolve b5e2307 b5e2583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2307 b5e2583
          have b5e9055 : (M.op (σ y) (σ (M.op x x))) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e9049
               have i₂ := b5e91 y (σ y) y
               grind)
            | exact superpose b5e91 b5e9049
            | exact resolve b5e9049 b5e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91 b5e9049
          have b5e9083 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op (M.op y y) y)) := by
            first
            | (have i₁ := b5e9055
               have i₂ := b5e2293 y
               grind)
            | exact superpose b5e2293 b5e9055
            | exact resolve b5e9055 b5e2293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2293 b5e9055
          have b5e9096 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op y (M.op y y))) := by
            first
            | (have i₁ := b5e9083
               have i₂ := b5e13 y y y
               grind)
            | exact superpose b5e13 b5e9083
            | exact resolve b5e9083 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9083
          have b5e9104 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b5e9096
               have i₂ := b5e342 y
               grind)
            | (have i₁ := b5e9096
               have i₂ := b5e342 (M.op y y)
               grind)
            | exact superpose b5e342 b5e9096
            | exact resolve b5e9096 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e342 b5e9096
          have b5e9109 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e9104
               have i₂ := b5e8973 x
               grind)
            | exact superpose b5e8973 b5e9104
            | exact resolve b5e9104 b5e8973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8973 b5e9104
          have b5e9112 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e9109
               have i₂ := b5e1729
               grind)
            | exact superpose b5e1729 b5e9109
            | exact resolve b5e9109 b5e1729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1729 b5e9109
          have b5e9114 : False := by grind
          exact b5e9114
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 X3
               have i₂ := b7e13 X1 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 X2) X3 X1
               have i₂ := b7e13 X1 X2 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X2 (M.op x X0)
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
          have b7e50 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear b7e47
          have b7e52 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e53 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e52
            | exact resolve b7e52 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e54 : (σ (M.op x x)) = (σ (k x y)) := by
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
          have b7e57 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e14
            | exact resolve b7e14 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b7e64 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op y x) ∨ x = y := by
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
          have b7e65 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e66 : (σ (M.op x y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e21
               grind)
            | exact resolve b7e65 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e69 : (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e122 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X0 (σ x) X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e123 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 X1 (σ X0) X2 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e33
            | exact resolve b7e33 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e158 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X1)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 (M.op X1 X1)
               have i₂ := b7e13 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b7e13 b7e35
            | exact resolve b7e35 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e161 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b7e35 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e35
            | exact resolve b7e35 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e170 : ∀ X1 : G, (M.op (σ y) (M.op X1 X1)) = (M.op (σ x) (M.op X1 (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b7e158 x X1
               have i₂ := b7e37 x X1 X1
               grind)
            | exact superpose b7e37 b7e158
            | exact resolve b7e158 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37 b7e158
          have b7e796 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b7e122 (σ x) X0
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e122
            | exact resolve b7e122 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e814 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e36 x x (σ x) X0
               have i₂ := b7e122 (M.op x x) X0
               grind)
            | exact superpose b7e122 b7e36
            | exact resolve b7e36 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e122
          have b7e842 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e814 X0
               have i₂ := b7e123 x (σ x) (M.op X0 X0)
               grind)
            | exact superpose b7e123 b7e814
            | exact resolve b7e814 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123 b7e814
          have b7e849 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e796 X0
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e796
            | exact resolve b7e796 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e796
          have b7e855 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e842 X0
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e842
            | exact resolve b7e842 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e842
          have b7e863 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e855 X0
               have i₂ := b7e849 (M.op X0 X0)
               grind)
            | exact superpose b7e849 b7e855
            | exact resolve b7e855 b7e849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e849 b7e855
          have b7e2870 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have i₁ := b7e161 x
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e161
            | exact resolve b7e161 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66 b7e161
          have b7e2890 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have i₁ := b7e2870
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2870
            | exact resolve b7e2870 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2870
          have b7e7428 : (M.op (σ y) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b7e170 (σ x)
               have i₂ := b7e35 (σ x)
               grind)
            | exact superpose b7e35 b7e170
            | exact resolve b7e170 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e170
          have b7e7464 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e7428
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e7428
            | exact resolve b7e7428 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7428
          have b7e7518 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e7464
               have i₂ := b7e863 (σ x)
               grind)
            | exact superpose b7e863 b7e7464
            | exact resolve b7e7464 b7e863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e863 b7e7464
          have b7e7559 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e7518
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e7518
            | exact resolve b7e7518 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7518
          have b7e7674 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e7559
               grind)
            | exact superpose b7e7559 b7e20
            | exact resolve b7e20 b7e7559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7675 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e62 y x
               have i₂ := b7e7559
               grind)
            | exact superpose b7e7559 b7e62
            | (have j0 := b7e62 y x
               grind)
            | exact resolve b7e62 b7e7559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e7559
          have b7e7691 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
          clear b7e7675
          have b7e7695 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have r₁ := b7e7691
               have r₂ := b7e23
               grind)
            | exact resolve b7e7691 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7691
          have b7e7697 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e7695
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e7695
            | exact resolve b7e7695 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7695
          have b7e8897 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e7697
               grind)
            | exact superpose b7e7697 b7e14
            | exact resolve b7e14 b7e7697
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7697
          have b7e8938 : y = (k y x) := by
            first
            | (have i₁ := b7e8897
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e8897
            | exact resolve b7e8897 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8897
          have b7e9768 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 y x
               have i₂ := b7e8938
               grind)
            | exact superpose b7e8938 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e8938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8938
          have b7e9769 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e9768
               have r₂ := b7e22
               grind)
            | exact resolve b7e9768 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9768
          have b7e9771 : x = (M.op x y) := by
            first
            | (have r₁ := b7e9769
               have r₂ := b7e21
               grind)
            | exact resolve b7e9769 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9769
          have b7e11224 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e2890
               have i₂ := b7e9771
               grind)
            | exact superpose b7e9771 b7e2890
            | exact resolve b7e2890 b7e9771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2890 b7e9771
          have b7e11255 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e11224
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e11224
            | exact resolve b7e11224 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e11224
          have b7e11260 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b7e11255
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e11255
            | exact resolve b7e11255 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e11255
          have b7e11263 : False := by grind
          exact b7e11263
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
          have b8e1016 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
          have b8e1049 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1016
               have r₂ := b8e24
               grind)
            | exact resolve b8e1016 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1016
          have b8e1062 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1049
               have r₂ := b8e23
               grind)
            | exact resolve b8e1049 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1049
          have b8e1067 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1062
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1062
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1062
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1062
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1062 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1062
          have b8e1068 : y = (M.op y x) ∨ x = y := by grind
          clear b8e1067
          have b8e1069 : x = y := by
            first
            | (have r₁ := b8e1068
               have r₂ := b8e22
               grind)
            | exact resolve b8e1068 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1068
          have b8e1070 : False := by grind
          exact b8e1070

/-- `Equation4520`: `x ◇ (y ◇ z) = (x ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation4520 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4520 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4520.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
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
          have b4e39 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) X0 X1 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 X2 x
               have i₂ := b4e13 X0 X3 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : y = (M.op y y) := by
            first
            | (have i₁ := b4e40 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e40
            | exact resolve b4e40 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e109 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (σ X0) X1 X2 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e13
            | exact resolve b4e13 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e136 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ x) x
               have i₂ := b4e34 X0 x
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e140 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (σ y)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X0 X1) X2 X3 (σ x)
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e141 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X3) (σ x)) = (M.op X1 (M.op X0 (σ y))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 X1 (M.op X0 x) (σ x) X3
               have i₂ := b4e34 X0 x
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e142 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e141 X0 X1 x
               have i₂ := b4e34 X1 x
               grind)
            | exact superpose b4e34 b4e141
            | exact resolve b4e141 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e141
          have b4e272 : (M.op (σ y) x) = (M.op (σ y) y) := by
            first
            | (have i₁ := b4e39 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e292 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op X0 (M.op (σ y) y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ y) x X1
               have i₂ := b4e272
               grind)
            | exact superpose b4e272 b4e13
            | exact resolve b4e13 b4e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272
          have b4e342 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 X1 y y
               have i₂ := b4e46
               grind)
            | exact superpose b4e46 b4e41
            | exact resolve b4e41 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e46
          have b4e2807 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b4e136 X0 (σ x)
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e136
            | exact resolve b4e136 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136
          have b4e3319 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ (M.op X0 X0)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e142 x (σ X0)
               have i₂ := b4e109 X0 x (σ y)
               grind)
            | exact superpose b4e109 b4e142
            | exact resolve b4e142 b4e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109 b4e142
          have b4e3608 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b4e30 (M.op x x)
               have i₂ := b4e2807 (σ (M.op x x))
               grind)
            | exact superpose b4e2807 b4e30
            | exact resolve b4e30 b4e2807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e2807
          have b4e3615 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b4e3608
               have i₂ := b4e3319 x
               grind)
            | exact superpose b4e3319 b4e3608
            | exact resolve b4e3608 b4e3319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3319 b4e3608
          have b4e3651 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x (σ y)) x)) := by
            first
            | (have i₁ := b4e3615
               have i₂ := b4e140 x x x x
               grind)
            | exact superpose b4e140 b4e3615
            | exact resolve b4e3615 b4e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e140 b4e3615
          have b4e3683 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op (σ y) y))) := by
            first
            | (have i₁ := b4e3651
               have i₂ := b4e292 x (σ y)
               grind)
            | exact superpose b4e292 b4e3651
            | exact resolve b4e3651 b4e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292 b4e3651
          have b4e3709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e3683
               have i₂ := b4e342 x (σ y)
               grind)
            | exact superpose b4e342 b4e3683
            | exact resolve b4e3683 b4e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342 b4e3683
          have b4e3724 : False := by grind
          exact b4e3724
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
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
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e36 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 y X0 X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : y = (M.op y y) := by
            first
            | (have i₁ := b5e36 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e36
            | exact resolve b5e36 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e53 : x = y ∨ x = (k x y) := by grind
          clear b5e49
          have b5e54 : x = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e21
               grind)
            | exact resolve b5e53 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e98 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X1 X2 (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1939 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op y (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e36 (σ X0) (σ X1)
               have i₂ := b5e57 X0 X1
               grind)
            | exact superpose b5e57 b5e36
            | (have j1 := b5e57 X0 X1
               grind)
            | exact resolve b5e36 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e57
          have b5e2214 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e98 y X0 X1
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e98
            | exact resolve b5e98 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e63003 : (M.op y (σ y)) = (M.op y (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1939 x y
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e1939
            | (have j0 := b5e1939 x y
               grind)
            | exact resolve b5e1939 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e1939
          have b5e63133 : (M.op y (σ y)) = (M.op y (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e63003
               have r₂ := b5e24
               grind)
            | exact resolve b5e63003 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63003
          have b5e63139 : (M.op y (σ y)) = (M.op y (σ x)) := by
            first
            | (have r₁ := b5e63133
               have r₂ := b5e23
               grind)
            | exact resolve b5e63133 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63133
          have b5e63237 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op y (σ y))) := by
            first
            | (have i₁ := b5e2214 y (σ x)
               have i₂ := b5e63139
               grind)
            | exact superpose b5e63139 b5e2214
            | exact resolve b5e2214 b5e63139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63139
          have b5e63240 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e63237
               have i₂ := b5e2214 y (σ y)
               grind)
            | exact superpose b5e2214 b5e63237
            | exact resolve b5e63237 b5e2214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2214 b5e63237
          have b5e63270 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e63240
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e63240
            | exact resolve b5e63240 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e63240
          have b5e63299 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e63270
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e63270
            | exact resolve b5e63270 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e63270
          have b5e63325 : False := by grind
          exact b5e63325
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
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
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
          have b7e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2 x
               have i₂ := b7e13 X0 X3 X2 x
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
          clear b7e54
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
          have b7e101 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e32 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e110 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e101
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e101
            | exact resolve b7e101 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e101
          have b7e114 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e110
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e110
            | exact resolve b7e110 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e191 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e114
               grind)
            | exact superpose b7e114 b7e14
            | exact resolve b7e14 b7e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e114
          have b7e192 : y = (M.op y y) := by
            first
            | (have i₁ := b7e191
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e191
            | exact resolve b7e191 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e191
          have b7e255 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e40 X0 X1 y x
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e40
            | exact resolve b7e40 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e256 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e40 X0 X1 y y
               have i₂ := b7e192
               grind)
            | exact superpose b7e192 b7e40
            | exact resolve b7e40 b7e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e301 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e255 X0 x
               have i₂ := b7e256 X0 x
               grind)
            | exact superpose b7e256 b7e255
            | exact resolve b7e255 b7e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e255 b7e256
          have b7e327 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e301 y
               grind)
            | exact superpose b7e301 b7e22
            | exact resolve b7e22 b7e301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e301
          have b7e328 : False := by grind
          exact b7e328
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
          have b8e1601 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
          have b8e1672 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1601
               have r₂ := b8e24
               grind)
            | exact resolve b8e1601 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1601
          have b8e1681 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1672
               have r₂ := b8e23
               grind)
            | exact resolve b8e1672 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1672
          have b8e1686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1681
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1681
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1681
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1681
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1681 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1681
          have b8e1687 : y = (M.op y x) ∨ x = y := by grind
          clear b8e1686
          have b8e1688 : x = y := by
            first
            | (have r₁ := b8e1687
               have r₂ := b8e22
               grind)
            | exact resolve b8e1687 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1687
          have b8e1689 : False := by grind
          exact b8e1689
