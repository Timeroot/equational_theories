import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyy_y_pxx_pxy_Equation3284 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3284 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e33 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
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
      have b0e34 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) x (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op X1 X0) X2 X2
           have i₂ := b0e11 X0 X2 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
        intro X0 X1 X2
        grind
      have b0e41 : ∀ X0 : G, (M.op X0 y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 X0
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e15
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e46 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e55 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0
           have i₂ := b0e41 X1
           grind)
        | (have i₁ := b0e41 X0
           have i₂ := b0e41 y
           grind)
        | exact superpose b0e41 b0e41
        | exact resolve b0e41 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 y
           have i₂ := b0e41 X0
           grind)
        | (have i₁ := b0e15 y y
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e15
        | (have j0 := b0e15 X0 y
           grind)
        | (have r₁ := b0e15 X0 y
           have r₂ := b0e41 X0
           grind)
        | (have r₁ := b0e15 y y
           have r₂ := b0e41 y
           grind)
        | exact resolve b0e15 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ y = (M.op X0 y) ∨ (M.op X0 y) = (k y y) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 y
           have i₂ := b0e41 X0
           grind)
        | (have i₁ := b0e15 y y
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e15
        | (have r₁ := b0e15 X0 y
           have r₂ := b0e41 X0
           grind)
        | (have r₁ := b0e15 y y
           have r₂ := b0e41 y
           grind)
        | exact resolve b0e15 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e64 : ∀ X0 : G, (M.op X0 y) = (k y y) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e62 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have j0 := b0e57 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e117 : ∀ X0 X1 : G, y = (M.op X1 (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 X1
           have i₂ := b0e55 X1 X0
           grind)
        | (have i₁ := b0e33 X1
           have i₂ := b0e55 X0 X1
           grind)
        | exact superpose b0e55 b0e33
        | exact resolve b0e33 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e143 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) X0 X0
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e158 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e174 : ∀ X0 : G, y = (k (M.op X0 y) y) := by
        intro X0
        grind
      clear b0e117
      have b0e260 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X3 (M.op X0 (M.op X1 X1)))) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e11 (M.op X1 X0) X1 (M.op X1 X0)
           have i₂ := b0e37 X0 X1 x
           grind)
        | (have i₁ := b0e11 (M.op X0 X0) X1 x
           have i₂ := b0e37 X0 X1 x
           grind)
        | exact superpose b0e37 b0e11
        | exact resolve b0e11 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e655 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e143 X0
           have i₂ := b0e143 X1
           grind)
        | (have i₁ := b0e143 X0
           have i₂ := b0e143 (σ y)
           grind)
        | exact superpose b0e143 b0e143
        | exact resolve b0e143 b0e143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e671 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) (M.op X0 (σ y))) := by
        intro X0
        grind
      clear b0e143
      have b0e695 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ y))) = (k (M.op X1 (σ y)) (M.op X0 (M.op X0 (σ y)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 X0 (M.op X0 (σ y))
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e39
        | exact resolve b0e39 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e750 : ∀ X1 : G, (σ y) = (k (M.op X1 (σ y)) (σ y)) := by
        intro X1
        first
        | (have i₁ := b0e695 x X1
           have i₂ := b0e34 x
           grind)
        | exact superpose b0e34 b0e695
        | exact resolve b0e695 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e695
      have b0e805 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e655 (σ x) X0
           grind)
        | (have i₁ := b0e18
           have i₂ := b0e655 X0 (σ x)
           grind)
        | exact superpose b0e655 b0e18
        | exact resolve b0e18 b0e655
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e655
      have b0e981 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e805 X1
           have i₂ := b0e55 x X0
           grind)
        | (have i₁ := b0e805 X1
           have i₂ := b0e55 X0 x
           grind)
        | exact superpose b0e55 b0e805
        | exact resolve b0e805 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e805
      have b0e1314 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 (M.op X1 (M.op X2 X0))) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e51 X1 X2 X0
           grind)
        | exact superpose b0e51 b0e11
        | (have j1 := b0e51 X1 X2 X0
           grind)
        | exact resolve b0e11 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e1427 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op X0 (σ y))) y) := by
        intro X0
        first
        | (have i₁ := b0e31 (M.op X0 (σ y)) y
           have i₂ := b0e750 X0
           grind)
        | exact superpose b0e750 b0e31
        | exact resolve b0e31 b0e750
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e750
      have b0e1428 : ∀ X0 : G, y = (k (τ (M.op X0 (σ y))) y) := by
        intro X0
        first
        | (have i₁ := b0e1427 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e1427
        | exact resolve b0e1427 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1427
      have b0e5080 : ∀ X0 X1 : G, (M.op X0 y) = (k y y) ∨ y = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e55 X0 X1
           have i₂ := b0e64 X1
           grind)
        | exact superpose b0e64 b0e55
        | (have j1 := b0e64 X0
           grind)
        | exact resolve b0e55 b0e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e5086 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (σ (k y y)) ∨ y = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e981 X1 X0
           have i₂ := b0e64 X1
           grind)
        | exact superpose b0e64 b0e981
        | (have j1 := b0e64 X1
           grind)
        | exact resolve b0e981 b0e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e6110 : ∀ X0 : G, y ≠ (k X0 y) ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have j0 := b0e65 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e6986 : ∀ X0 : G, y ≠ y ∨ y = (M.op (τ (M.op X0 (σ y))) (τ (M.op X0 (σ y)))) := by
        intro X0
        first
        | (have i₁ := b0e6110 (τ (M.op X0 (σ y)))
           have i₂ := b0e1428 X0
           grind)
        | exact superpose b0e1428 b0e6110
        | (have j0 := b0e6110 (τ (M.op X0 (σ y)))
           grind)
        | (have r₁ := b0e6110 (τ (M.op X0 (σ y)))
           have r₂ := b0e1428 X0
           grind)
        | exact resolve b0e6110 b0e1428
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1428 b0e6110
      have b0e6990 : ∀ X0 : G, y = (M.op (τ (M.op X0 (σ y))) (τ (M.op X0 (σ y)))) := by
        intro X0
        first
        | (have j0 := b0e6986 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6986
      have b0e8553 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (k y (τ (M.op X0 (σ y)))) := by
        intro X0
        first
        | (have i₁ := b0e158 y (M.op X0 (σ y))
           have i₂ := b0e671 X0
           grind)
        | exact superpose b0e671 b0e158
        | exact resolve b0e158 b0e671
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e158 b0e671
      have b0e8880 : ∀ X1 : G, (M.op X1 y) = (k y y) ∨ y = (k y y) := by
        intro X1
        first
        | (have i₁ := b0e174 x
           have i₂ := b0e5080 X1 x
           grind)
        | exact superpose b0e5080 b0e174
        | (have j1 := b0e5080 X1 X1
           grind)
        | exact resolve b0e174 b0e5080
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e174 b0e5080
      have b0e10748 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (k y y)) ∨ y = (k y y) := by
        intro X0
        first
        | (have i₁ := b0e981 x X0
           have i₂ := b0e8880 x
           grind)
        | exact superpose b0e8880 b0e981
        | exact resolve b0e981 b0e8880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8880
      have b0e18582 : ∀ X0 X2 : G, (M.op X2 (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e260 (M.op X2 X0) (M.op X2 X0) x
           have i₂ := b0e1314 X0 (M.op X2 X0) X2
           grind)
        | exact superpose b0e1314 b0e260
        | (have j1 := b0e1314 X0 x X2
           grind)
        | exact resolve b0e260 b0e1314
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e260
      have b0e65438 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e1314 X0 X1 X1
           have i₂ := b0e18582 X0 X1
           grind)
        | exact superpose b0e18582 b0e1314
        | (have j0 := b0e1314 X0 X1 x
           have j1 := b0e18582 X0 x
           grind)
        | exact resolve b0e1314 b0e18582
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1314 b0e18582
      have b0e65615 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e65438 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65438
      have b0e67835 : y = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b0e6990 x
           have i₂ := b0e65615 (σ y) x
           grind)
        | exact superpose b0e65615 b0e6990
        | (have j1 := b0e65615 (σ y) x
           grind)
        | exact resolve b0e6990 b0e65615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6990
      have b0e67836 : (τ (σ y)) = (k y (τ (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b0e8553 x
           have i₂ := b0e65615 (σ y) x
           grind)
        | exact superpose b0e65615 b0e8553
        | (have j1 := b0e65615 (σ y) x
           grind)
        | exact resolve b0e8553 b0e65615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8553
      have b0e68039 : y = (k y y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b0e67836
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e67836
        | exact resolve b0e67836 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67836
      have b0e68040 : y = (M.op y y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b0e67835
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e67835
        | exact resolve b0e67835 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67835
      have b0e68137 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b0e68039
           have i₂ := b0e17 y y
           grind)
        | exact superpose b0e17 b0e68039
        | exact resolve b0e68039 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68039
      have b0e68138 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e68040
           have i₂ := b0e17 y y
           grind)
        | exact superpose b0e17 b0e68040
        | exact resolve b0e68040 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68040
      have b0e68161 : y = (k y y) := by
        first
        | (have r₁ := b0e68137
           have r₂ := b0e10748 (σ y)
           grind)
        | exact resolve b0e68137 b0e10748
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10748 b0e68137
      have b0e68162 : y = (M.op y y) := by
        first
        | (have j1 := b0e5086 x y
           grind)
        | (have r₁ := b0e68138
           have r₂ := b0e5086 (σ y) x
           grind)
        | exact resolve b0e68138 b0e5086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5086 b0e68138
      have b0e70875 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e981 y X0
           have i₂ := b0e68162
           grind)
        | exact superpose b0e68162 b0e981
        | exact resolve b0e981 b0e68162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e981 b0e68162
      have b0e72098 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b0e70875 x
           have i₂ := b0e65615 (σ y) x
           grind)
        | exact superpose b0e65615 b0e70875
        | (have j1 := b0e65615 (σ y) x
           grind)
        | (have r₁ := b0e70875 x
           have r₂ := b0e65615 (σ y) x
           grind)
        | exact resolve b0e70875 b0e65615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65615
      have b0e72106 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
      clear b0e72098
      have b0e72107 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
        first
        | (have i₁ := b0e72106
           have i₂ := b0e17 y y
           grind)
        | exact superpose b0e17 b0e72106
        | exact resolve b0e72106 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72106
      have b0e72110 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e72107
           have i₂ := b0e68161
           grind)
        | exact superpose b0e68161 b0e72107
        | exact resolve b0e72107 b0e68161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68161 b0e72107
      have b0e72111 : False := by grind
      exact b0e72111
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e59 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e3879 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b1e59 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e3884 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e3879
             have r₂ := b1e21
             grind)
          | exact resolve b1e3879 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3879
        have b1e3888 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e3884
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e3884
          | exact resolve b1e3884 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3884
        have b1e3890 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e3888
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e3888
          | exact resolve b1e3888 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e3888
        have b1e3892 : False := by grind
        exact b1e3892
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e99 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b2e1795 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e99 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99
        have b2e1796 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1795
             have r₂ := b2e22
             grind)
          | exact resolve b2e1795 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1795
        have b2e1797 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1796
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1796
          | exact resolve b2e1796 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1796
        have b2e1798 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1797
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1797
          | exact resolve b2e1797 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1797
        have b2e1800 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b2e12 (σ y) X0 (σ x)
             have i₂ := b2e1798
             grind)
          | exact superpose b2e1798 b2e12
          | exact resolve b2e12 b2e1798
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3450 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1800 (σ x)
             have i₂ := b2e1798
             grind)
          | exact superpose b2e1798 b2e1800
          | exact resolve b2e1800 b2e1798
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1798 b2e1800
        have b2e3510 : False := by grind
        exact b2e3510
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ y) = (σ (k x y)) := by
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
        have b3e27 : (k x y) = (τ (σ y)) := by
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
        have b3e28 : y = (k x y) := by
          first
          | (have i₁ := b3e27
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e27
          | exact resolve b3e27 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e51 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = y ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e823 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e51 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e825 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e823
             have r₂ := b3e20
             grind)
          | exact resolve b3e823 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e823
        have b3e826 : y = (M.op x x) := by
          first
          | (have i₁ := b3e825
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e825
          | exact resolve b3e825 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e825
        have b3e827 : False := by grind
        exact b3e827
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b4e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e39 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X1 X0) X2 X2
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2
            grind
          have b4e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b4e52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e34
            | exact resolve b4e34 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e61 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e17
            | exact resolve b4e17 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e61 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61
          have b4e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
          have b4e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88
          have b4e106 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e105 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e123 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e64 (σ X0)
               grind)
            | exact superpose b4e64 b4e19
            | (have j1 := b4e64 (σ X0)
               grind)
            | exact resolve b4e19 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e138 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e39 X1 x X3
               have i₂ := b4e39 X1 x X0
               grind)
            | (have i₁ := b4e39 X0 X0 x
               have i₂ := b4e39 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b4e39 b4e39
            | exact resolve b4e39 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e162 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X2 X1) = (M.op X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X2 X1) (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 (M.op X1 X0) (M.op X1 X0)
               have i₂ := b4e39 X0 X1 X2
               grind)
            | (have i₁ := b4e17 X2 (M.op X0 X0)
               have i₂ := b4e39 X0 X1 X2
               grind)
            | exact superpose b4e39 b4e17
            | (have r₁ := b4e17 (M.op X0 X0) (M.op X0 X0)
               have r₂ := b4e39 X0 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b4e17 X2 (M.op X1 X1)
               have r₂ := b4e39 X1 X1 X2
               grind)
            | exact resolve b4e17 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e174 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X2 X1) (M.op X2 X1)) ∨ (M.op X2 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e162 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e162
          have b4e188 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e48
          have b4e644 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 (M.op X1 (τ X2))))) = (k X2 (σ (M.op X0 (M.op X0 (M.op X1 (τ X2)))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e28 X2 (M.op X0 (M.op X0 (M.op X1 (τ X2))))
               have i₂ := b4e41 X0 X1 (τ X2)
               grind)
            | exact superpose b4e41 b4e28
            | exact resolve b4e28 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1171 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e106 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e106
          have b4e1353 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 (M.op X1 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e66 X1 X2 X0
               grind)
            | exact superpose b4e66 b4e13
            | (have j1 := b4e66 X1 X2 X0
               grind)
            | exact resolve b4e13 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e15899 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e41 x x X0
               have i₂ := b4e1353 X0 x x
               grind)
            | exact superpose b4e1353 b4e41
            | (have j1 := b4e1353 X0 x x
               grind)
            | exact resolve b4e41 b4e1353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e16155 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e15899 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15899
          have b4e22554 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e123 y
               grind)
            | exact superpose b4e123 b4e27
            | (have j1 := b4e123 y
               grind)
            | exact resolve b4e27 b4e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e22662 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e123 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123
          have b4e46057 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e644 x x x
               have i₂ := b4e1353 (τ x) x x
               grind)
            | exact superpose b4e1353 b4e644
            | (have j1 := b4e1353 (τ X0) x x
               grind)
            | exact resolve b4e644 b4e1353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e644 b4e1353
          have b4e46142 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e46057 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e46057
            | (have j0 := b4e46057 X0
               grind)
            | exact resolve b4e46057 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46057
          have b4e46194 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e46142 X0
               have i₂ := b4e52 X0 X0
               grind)
            | exact superpose b4e52 b4e46142
            | (have j0 := b4e46142 X0
               grind)
            | exact resolve b4e46142 b4e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e46142
          have b4e46206 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e46194 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e46194
            | (have j0 := b4e46194 (σ X0)
               grind)
            | exact resolve b4e46194 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46194
          have b4e46420 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e46206 X0
               have i₂ := b4e34 (σ X0) X0
               grind)
            | exact superpose b4e34 b4e46206
            | (have j0 := b4e46206 X0
               grind)
            | exact resolve b4e46206 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e46206
          have b4e46424 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e46420 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e46420
            | (have j0 := b4e46420 X0
               grind)
            | exact resolve b4e46420 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46420
          have b4e46425 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e46424 X0
               have i₂ := b4e19 X0 X0
               grind)
            | exact superpose b4e19 b4e46424
            | (have j0 := b4e46424 X0
               grind)
            | exact resolve b4e46424 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46424
          have b4e47233 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e22662 X0
               have i₂ := b4e46425 X0
               grind)
            | exact superpose b4e46425 b4e22662
            | (have j0 := b4e22662 X0
               have j1 := b4e46425 X0
               grind)
            | (have r₁ := b4e22662 X0
               have r₂ := b4e46425 X0
               grind)
            | exact resolve b4e22662 b4e46425
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46425
          have b4e47263 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e47233 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47233
          have b4e47567 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e138 X0 (σ X0) x
               have i₂ := b4e47263 X0
               grind)
            | exact superpose b4e47263 b4e138
            | (have j1 := b4e47263 X0
               grind)
            | exact resolve b4e138 b4e47263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138
          have b4e99743 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e47263 X1
               have i₂ := b4e47567 X1 X0 (σ X1)
               grind)
            | (have i₁ := b4e47263 X1
               have i₂ := b4e47567 X1 (σ X1) X0
               grind)
            | exact superpose b4e47567 b4e47263
            | (have j0 := b4e47263 X1
               have j1 := b4e47567 X1 X1 x
               grind)
            | exact resolve b4e47263 b4e47567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47263 b4e47567
          have b4e99795 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e99743 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99743
          have b4e100997 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op X1 (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 (τ X0)
               have i₂ := b4e99795 X1 (τ X0)
               grind)
            | exact superpose b4e99795 b4e28
            | (have j1 := b4e99795 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e99795
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e99795
          have b4e101014 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (τ X0)) = (M.op X1 (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e100997 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e100997
            | (have j0 := b4e100997 X0 X1
               grind)
            | exact resolve b4e100997 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100997
          have b4e101047 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e101014 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e101014
            | (have j0 := b4e101014 X0 X1
               grind)
            | exact resolve b4e101014 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101014
          have b4e101785 : ∀ X0 X1 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e101047 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e101047
            | (have j0 := b4e101047 (σ X0) X1
               grind)
            | exact resolve b4e101047 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101047
          have b4e101924 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e101785 X0 X1
               have i₂ := b4e19 X0 X0
               grind)
            | exact superpose b4e19 b4e101785
            | (have j0 := b4e101785 X0 X1
               grind)
            | exact resolve b4e101785 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101785
          have b4e134572 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e16155 (σ X0)
               have i₂ := b4e101924 X0 (σ X0)
               grind)
            | exact superpose b4e101924 b4e16155
            | (have j0 := b4e16155 (σ X0)
               have j1 := b4e101924 X0 x
               grind)
            | (have r₁ := b4e16155 (σ X0)
               have r₂ := b4e101924 X0 (σ X0)
               grind)
            | exact resolve b4e16155 b4e101924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16155 b4e101924
          have b4e134612 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b4e134572 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134572
          have b4e134618 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e134612 X0
               have i₂ := b4e19 X0 X0
               grind)
            | exact superpose b4e19 b4e134612
            | (have j0 := b4e134612 X0
               grind)
            | exact resolve b4e134612 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134612
          have b4e150465 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b4e22554
               have i₂ := b4e134618 y
               grind)
            | exact superpose b4e134618 b4e22554
            | (have j1 := b4e134618 y
               grind)
            | (have r₁ := b4e22554
               have r₂ := b4e134618 y
               grind)
            | exact resolve b4e22554 b4e134618
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22554 b4e134618
          have b4e150473 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y y)) := by grind
          clear b4e150465
          have b4e150479 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have j1 := b4e22662 y
               grind)
            | (have r₁ := b4e150473
               have r₂ := b4e22662 y
               grind)
            | exact resolve b4e150473 b4e22662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22662 b4e150473
          have b4e152505 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e150479
               grind)
            | exact superpose b4e150479 b4e27
            | exact resolve b4e27 b4e150479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e152506 : (τ (σ y)) = (k y (τ (σ y))) := by
            first
            | (have i₁ := b4e188 y
               have i₂ := b4e150479
               grind)
            | exact superpose b4e150479 b4e188
            | exact resolve b4e188 b4e150479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188 b4e150479
          have b4e152754 : y = (k y y) := by
            first
            | (have i₁ := b4e152506
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e152506
            | exact resolve b4e152506 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152506
          have b4e153531 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e1171 y y
               have i₂ := b4e152754
               grind)
            | exact superpose b4e152754 b4e1171
            | (have j0 := b4e1171 y y
               grind)
            | (have r₁ := b4e1171 y y
               have r₂ := b4e152754
               grind)
            | exact resolve b4e1171 b4e152754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1171
          have b4e153536 : y ≠ y ∨ y = (M.op y y) := by grind
          clear b4e153531
          have b4e153537 : y = (M.op y y) := by grind
          clear b4e153536
          have b4e154000 : ∀ X0 : G, (k y y) = (M.op X0 y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e174 X0 y y
               have i₂ := b4e153537
               grind)
            | exact superpose b4e153537 b4e174
            | exact resolve b4e174 b4e153537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e174 b4e153537
          have b4e154166 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e154000 X0
               have i₂ := b4e152754
               grind)
            | exact superpose b4e152754 b4e154000
            | (have j0 := b4e154000 X0
               grind)
            | exact resolve b4e154000 b4e152754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152754 b4e154000
          have b4e154167 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e154166 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154166
          have b4e157523 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e152505
               have i₂ := b4e154167 y
               grind)
            | exact superpose b4e154167 b4e152505
            | exact resolve b4e152505 b4e154167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152505 b4e154167
          have b4e157533 : False := by grind
          exact b4e157533
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b5e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e27 X0 X1
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X3 (M.op X4 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X2 X3 X4
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X3 (M.op X0 (M.op X0 (M.op X1 X2))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X3 (M.op X3 (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X1 (M.op X2 X0)) X3 X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X1 X0) X2 X2
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2
            grind
          have b5e41 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37 X0 X1 X2 x
               have i₂ := b5e13 X0 x X0
               grind)
            | exact superpose b5e13 b5e37
            | exact resolve b5e37 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e33
            | exact resolve b5e33 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : (M.op y y) ≠ (M.op y y) ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e59 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X0 X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e59 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e63 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e58
          have b5e64 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e73 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b5e116 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e61 (σ X0)
               grind)
            | exact superpose b5e61 b5e19
            | (have j1 := b5e61 (σ X0)
               grind)
            | exact resolve b5e19 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e145 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e38 X1 x X3
               have i₂ := b5e38 X1 x X0
               grind)
            | (have i₁ := b5e38 X0 X0 x
               have i₂ := b5e38 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b5e38 b5e38
            | exact resolve b5e38 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e154 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e38 (M.op X3 X1) X2 X4
               have i₂ := b5e38 X1 X3 X0
               grind)
            | (have i₁ := b5e38 (M.op X0 X0) X1 X2
               have i₂ := b5e38 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b5e38 b5e38
            | exact resolve b5e38 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e167 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X2 X1) (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X2
            grind
          have b5e169 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X3 (M.op X0 (M.op X1 X1)))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 (M.op X1 X0) X1 (M.op X1 X0)
               have i₂ := b5e38 X0 X1 x
               grind)
            | (have i₁ := b5e13 (M.op X0 X0) X1 x
               have i₂ := b5e38 X0 X1 x
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X2 X2) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X2 (M.op X1 X1)
               have i₂ := b5e38 X1 X0 X2
               grind)
            | (have i₁ := b5e17 (M.op X1 X0) (M.op X1 X0)
               have i₂ := b5e38 X0 X1 X2
               grind)
            | exact superpose b5e38 b5e17
            | (have j0 := b5e17 X1 (M.op X2 X2)
               grind)
            | (have r₁ := b5e17 (M.op X0 X0) (M.op X0 X0)
               have r₂ := b5e38 X0 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b5e17 X2 (M.op X1 X1)
               have r₂ := b5e38 X1 X1 X2
               grind)
            | exact resolve b5e17 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e182 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X2 X2) := by
            intro X1 X2
            first
            | (have j0 := b5e178 x X1 X2
               grind)
            | (have r₁ := b5e178 X1 x X2
               have r₂ := b5e38 x X1 (M.op x x)
               grind)
            | (have r₁ := b5e178 X1 X1 X2
               have r₂ := b5e38 X1 X1 (M.op X1 X1)
               grind)
            | exact resolve b5e178 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e178
          have b5e184 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e154 X0 X1 x x X4
               have i₂ := b5e41 X1 x x
               grind)
            | exact superpose b5e41 b5e154
            | exact resolve b5e154 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e154
          have b5e282 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X3 (M.op X3 (M.op X4 (M.op X5 (M.op X6 X2))))) = (M.op X7 (M.op X7 (M.op X0 (M.op X0 (M.op X1 X2))))) := by
            intro X0 X1 X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b5e34 X3 X4 (M.op X5 (M.op X6 X2)) X7 X5
               have i₂ := b5e34 X5 X6 X2 X0 X1
               grind)
            | (have i₁ := b5e34 X3 X4 (M.op X5 (M.op X6 X2)) X7 X5
               have i₂ := b5e34 X0 X1 X2 X5 X6
               grind)
            | exact superpose b5e34 b5e34
            | exact resolve b5e34 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e283 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0))))) = (M.op X5 (M.op X5 (M.op X0 X0))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e34 X1 X2 (M.op X3 (M.op X4 X0)) X5 X3
               have i₂ := b5e13 X0 X3 X4
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e325 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e283 X0 X1 X2 X3 X4 x
               have i₂ := b5e13 X0 x X0
               grind)
            | exact superpose b5e13 b5e283
            | exact resolve b5e283 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e283
          have b5e764 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 (M.op X1 (τ X2))))) = (k X2 (σ (M.op X0 (M.op X0 (M.op X1 (τ X2)))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e27 X2 (M.op X0 (M.op X0 (M.op X1 (τ X2))))
               have i₂ := b5e40 X0 X1 (τ X2)
               grind)
            | exact superpose b5e40 b5e27
            | exact resolve b5e27 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e40
          have b5e1337 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 (M.op X1 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e62 X1 X2 X0
               grind)
            | exact superpose b5e62 b5e13
            | (have j1 := b5e62 X1 X2 X0
               grind)
            | exact resolve b5e13 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e1436 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e73 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e1437 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1436
               have r₂ := b5e24
               grind)
            | exact resolve b5e1436 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1436
          have b5e1438 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1437
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1437
            | exact resolve b5e1437 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1437
          have b5e1439 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1438
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e1438
            | exact resolve b5e1438 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e1438
          have b5e1440 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1439
               grind)
            | exact superpose b5e1439 b5e24
            | exact resolve b5e24 b5e1439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1441 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e26
               have i₂ := b5e1439
               grind)
            | exact superpose b5e1439 b5e26
            | exact resolve b5e26 b5e1439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e1442 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b5e13 (σ y) X0 (σ x)
               have i₂ := b5e1439
               grind)
            | exact superpose b5e1439 b5e13
            | exact resolve b5e13 b5e1439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1439
          have b5e12266 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e182 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182
          have b5e13481 : ∀ X0 X3 : G, (M.op X3 (M.op X3 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X3
            first
            | (have i₁ := b5e36 x x X0 X3
               have i₂ := b5e1337 X0 x x
               grind)
            | exact superpose b5e1337 b5e36
            | (have j1 := b5e1337 X0 x x
               grind)
            | exact resolve b5e36 b5e1337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e15782 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e145 X1 X0 X0
               have i₂ := b5e13481 X0 X0
               grind)
            | exact superpose b5e13481 b5e145
            | (have j1 := b5e13481 X0 x
               grind)
            | exact resolve b5e145 b5e13481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e15788 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e184 X0 X0 X1
               have i₂ := b5e13481 X0 X0
               grind)
            | exact superpose b5e13481 b5e184
            | (have j1 := b5e13481 X0 x
               grind)
            | exact resolve b5e184 b5e13481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13481
          have b5e16971 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e145 X0 (M.op X0 X0) x
               have i₂ := b5e15782 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e15782 b5e145
            | (have j1 := b5e15782 X0 X1
               grind)
            | exact resolve b5e145 b5e15782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16979 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e184 X0 (M.op X0 X0) x
               have i₂ := b5e15782 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e15782 b5e184
            | (have j1 := b5e15782 X0 X1
               grind)
            | exact resolve b5e184 b5e15782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15782
          have b5e17237 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e116 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116
          have b5e25541 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e16971 (σ y) X0 (σ x)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e16971 (σ y) (σ x) X0
               grind)
            | exact superpose b5e16971 b5e24
            | (have j1 := b5e16971 (σ y) x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e16971 (σ y) (σ y) (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e16971 (σ y) (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e16971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16971
          have b5e25622 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have j1 := b5e15788 (σ y) x
               grind)
            | (have r₁ := b5e25541 x
               have r₂ := b5e15788 (σ y) x
               grind)
            | (have r₁ := b5e25541 (σ y)
               have r₂ := b5e15788 (σ y) (σ y)
               grind)
            | exact resolve b5e25541 b5e15788
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15788 b5e25541
          have b5e25761 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b5e25622
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e25622
            | exact resolve b5e25622 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25622
          have b5e26036 : (σ (M.op x x)) ≠ (σ (k y y)) := by
            first
            | (have i₁ := b5e1440
               have i₂ := b5e25761
               grind)
            | exact superpose b5e25761 b5e1440
            | exact resolve b5e1440 b5e25761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26056 : ∀ X0 X1 : G, (M.op X1 (σ (k y y))) = (M.op X0 (σ (k y y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e145 X0 (σ y) x
               have i₂ := b5e25761
               grind)
            | exact superpose b5e25761 b5e145
            | exact resolve b5e145 b5e25761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26064 : ∀ X0 X1 : G, (σ (k y y)) = (M.op X0 (M.op X1 (σ (k y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e184 X0 (σ y) x
               have i₂ := b5e25761
               grind)
            | exact superpose b5e25761 b5e184
            | exact resolve b5e184 b5e25761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38798 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e764 x x x
               have i₂ := b5e1337 (τ x) x x
               grind)
            | exact superpose b5e1337 b5e764
            | (have j1 := b5e1337 (τ X0) x x
               grind)
            | exact resolve b5e764 b5e1337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e764 b5e1337
          have b5e38882 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b5e38798 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e38798
            | (have j0 := b5e38798 X0
               grind)
            | exact resolve b5e38798 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38798
          have b5e38931 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e38882 X0
               have i₂ := b5e50 X0 X0
               grind)
            | exact superpose b5e50 b5e38882
            | (have j0 := b5e38882 X0
               grind)
            | exact resolve b5e38882 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e38882
          have b5e39994 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e38931 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e38931
            | (have j0 := b5e38931 (σ X0)
               grind)
            | exact resolve b5e38931 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38931
          have b5e40199 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e39994 X0
               have i₂ := b5e33 (σ X0) X0
               grind)
            | exact superpose b5e33 b5e39994
            | (have j0 := b5e39994 X0
               grind)
            | exact resolve b5e39994 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39994
          have b5e40203 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e40199 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e40199
            | (have j0 := b5e40199 X0
               grind)
            | exact resolve b5e40199 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40199
          have b5e40204 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e40203 X0
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e40203
            | (have j0 := b5e40203 X0
               grind)
            | exact resolve b5e40203 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40203
          have b5e41233 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e17237 X0
               have i₂ := b5e40204 X0
               grind)
            | exact superpose b5e40204 b5e17237
            | (have j0 := b5e17237 X0
               have j1 := b5e40204 X0
               grind)
            | (have r₁ := b5e17237 X0
               have r₂ := b5e40204 X0
               grind)
            | exact resolve b5e17237 b5e40204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17237
          have b5e41239 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ (M.op y y) = (k y y) := by
            intro X0 X1
            first
            | (have i₁ := b5e26056 X0 X1
               have i₂ := b5e40204 y
               grind)
            | exact superpose b5e40204 b5e26056
            | (have j1 := b5e40204 y
               grind)
            | exact resolve b5e26056 b5e40204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26056 b5e40204
          have b5e41266 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e41233 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41233
          have b5e44574 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e145 X0 (σ X0) x
               have i₂ := b5e41266 X0
               grind)
            | exact superpose b5e41266 b5e145
            | (have j1 := b5e41266 X0
               grind)
            | exact resolve b5e145 b5e41266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44584 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op X2 (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e184 X0 (σ X0) x
               have i₂ := b5e41266 X0
               grind)
            | exact superpose b5e41266 b5e184
            | (have j1 := b5e41266 X0
               grind)
            | exact resolve b5e184 b5e41266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e184 b5e41266
          have b5e45474 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 (M.op X3 (σ (M.op x x))))))) = (M.op X4 (M.op X4 (M.op X5 (M.op (σ y) (σ y))))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e282 X5 X5 (σ (M.op x x)) X0 X1 X2 X3 X4
               have i₂ := b5e1442 X5
               grind)
            | exact superpose b5e1442 b5e282
            | exact resolve b5e282 b5e1442
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e282
          have b5e46557 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 (M.op X3 (σ (M.op x x))))))) = (M.op X5 (M.op (σ y) (σ y))) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b5e45474 X0 X1 X2 X3 x X5
               have i₂ := b5e169 X5 (σ y) x
               grind)
            | exact superpose b5e169 b5e45474
            | exact resolve b5e45474 b5e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e169 b5e45474
          have b5e46948 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 (M.op X3 (σ (M.op x x))))))) = (M.op X5 (σ (k y y))) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b5e46557 X0 X1 X2 X3 X5
               have i₂ := b5e25761
               grind)
            | exact superpose b5e25761 b5e46557
            | exact resolve b5e46557 b5e25761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25761 b5e46557
          have b5e47118 : ∀ X5 : G, (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op X5 (σ (k y y))) := by
            intro X5
            first
            | (have i₁ := b5e46948 x x x x X5
               have i₂ := b5e325 (σ (M.op x x)) x x x x
               grind)
            | exact superpose b5e325 b5e46948
            | exact resolve b5e46948 b5e325
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e325 b5e46948
          have b5e70766 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (σ (k y y)))) = (k (M.op X2 (σ (M.op x x))) (M.op X1 (M.op X0 (σ (k y y))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e167 X0 (σ (M.op x x)) X2
               have i₂ := b5e47118 x
               grind)
            | exact superpose b5e47118 b5e167
            | exact resolve b5e167 b5e47118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167
          have b5e70821 : ∀ X0 X1 : G, (σ (M.op x x)) = (M.op X1 (M.op X0 (σ (k y y)))) ∨ (k (σ (M.op x x)) (σ (M.op x x))) = (M.op X0 (σ (k y y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e16979 (σ (M.op x x)) X1 (σ (M.op x x))
               have i₂ := b5e47118 x
               grind)
            | exact superpose b5e47118 b5e16979
            | exact resolve b5e16979 b5e47118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16979
          have b5e70886 : ∀ X0 : G, (σ (M.op x x)) = (σ (k y y)) ∨ (k (σ (M.op x x)) (σ (M.op x x))) = (M.op X0 (σ (k y y))) := by
            intro X0
            first
            | (have i₁ := b5e70821 X0 x
               have i₂ := b5e26064 x X0
               grind)
            | exact superpose b5e26064 b5e70821
            | (have j0 := b5e70821 X0 x
               grind)
            | exact resolve b5e70821 b5e26064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70821
          have b5e70929 : ∀ X2 : G, (σ (k y y)) = (k (M.op X2 (σ (M.op x x))) (σ (k y y))) := by
            intro X2
            first
            | (have i₁ := b5e70766 x x X2
               have i₂ := b5e26064 x x
               grind)
            | exact superpose b5e26064 b5e70766
            | exact resolve b5e70766 b5e26064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26064 b5e70766
          have b5e70967 : ∀ X0 : G, (k (σ (M.op x x)) (σ (M.op x x))) = (M.op X0 (σ (k y y))) := by
            intro X0
            first
            | (have j0 := b5e70886 X0
               grind)
            | (have r₁ := b5e70886 X0
               have r₂ := b5e26036
               grind)
            | exact resolve b5e70886 b5e26036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26036 b5e70886
          have b5e71001 : ∀ X0 : G, (σ (k (M.op x x) (M.op x x))) = (M.op X0 (σ (k y y))) := by
            intro X0
            first
            | (have i₁ := b5e70967 X0
               have i₂ := b5e19 (M.op x x) (M.op x x)
               grind)
            | exact superpose b5e19 b5e70967
            | exact resolve b5e70967 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70967
          have b5e72082 : ∀ X0 : G, (k (M.op x x) (M.op x x)) = (τ (M.op X0 (σ (k y y)))) := by
            intro X0
            first
            | (have i₁ := b5e14 (k (M.op x x) (M.op x x))
               have i₂ := b5e71001 X0
               grind)
            | exact superpose b5e71001 b5e14
            | exact resolve b5e14 b5e71001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e88012 : ∀ X0 : G, (τ (σ (k y y))) = (k (τ (M.op X0 (σ (M.op x x)))) (k y y)) := by
            intro X0
            first
            | (have i₁ := b5e33 (M.op X0 (σ (M.op x x))) (k y y)
               have i₂ := b5e70929 X0
               grind)
            | exact superpose b5e70929 b5e33
            | exact resolve b5e33 b5e70929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33 b5e70929
          have b5e88013 : ∀ X0 : G, (k y y) = (k (τ (M.op X0 (σ (M.op x x)))) (k y y)) := by
            intro X0
            first
            | (have i₁ := b5e88012 X0
               have i₂ := b5e14 (k y y)
               grind)
            | exact superpose b5e14 b5e88012
            | exact resolve b5e88012 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88012
          have b5e90075 : ∀ X0 : G, (k y y) = (k (τ (M.op X0 (σ (k y y)))) (k y y)) := by
            intro X0
            first
            | (have i₁ := b5e88013 (σ (M.op x x))
               have i₂ := b5e47118 X0
               grind)
            | exact superpose b5e47118 b5e88013
            | exact resolve b5e88013 b5e47118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47118 b5e88013
          have b5e90083 : (k y y) = (k (k (M.op x x) (M.op x x)) (k y y)) := by
            first
            | (have i₁ := b5e90075 x
               have i₂ := b5e72082 x
               grind)
            | exact superpose b5e72082 b5e90075
            | exact resolve b5e90075 b5e72082
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90075
          have b5e105162 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op y y) = (k y y) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e44574 y X0 (σ x)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e44574 y (σ x) X0
               grind)
            | exact superpose b5e44574 b5e24
            | (have j1 := b5e44574 y x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e44574 y (σ y) (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e44574 y (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e44574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44574
          have b5e105219 : (M.op y y) = (k y y) := by
            first
            | (have r₁ := b5e105162 x
               have r₂ := b5e41239 x (σ y)
               grind)
            | (have r₁ := b5e105162 x
               have r₂ := b5e41239 (σ y) x
               grind)
            | exact resolve b5e105162 b5e41239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41239 b5e105162
          have b5e106761 : ∀ X0 : G, (σ (k (M.op x x) (M.op x x))) = (M.op X0 (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b5e71001 X0
               have i₂ := b5e105219
               grind)
            | exact superpose b5e105219 b5e71001
            | exact resolve b5e71001 b5e105219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71001
          have b5e106762 : ∀ X0 : G, (k (M.op x x) (M.op x x)) = (τ (M.op X0 (σ (M.op y y)))) := by
            intro X0
            first
            | (have i₁ := b5e72082 X0
               have i₂ := b5e105219
               grind)
            | exact superpose b5e105219 b5e72082
            | exact resolve b5e72082 b5e105219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72082
          have b5e106764 : (M.op y y) = (k (k (M.op x x) (M.op x x)) (M.op y y)) := by
            first
            | (have i₁ := b5e90083
               have i₂ := b5e105219
               grind)
            | exact superpose b5e105219 b5e90083
            | exact resolve b5e90083 b5e105219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90083 b5e105219
          have b5e118218 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op (k (M.op x x) (M.op x x)) (k (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b5e12266 (k (M.op x x) (M.op x x)) y
               have i₂ := b5e106764
               grind)
            | exact superpose b5e106764 b5e12266
            | (have j0 := b5e12266 y (k (M.op x x) (M.op x x))
               grind)
            | (have r₁ := b5e12266 (k (M.op x x) (M.op x x)) y
               have r₂ := b5e106764
               grind)
            | exact resolve b5e12266 b5e106764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12266 b5e106764
          have b5e118219 : (M.op y y) = (M.op (k (M.op x x) (M.op x x)) (k (M.op x x) (M.op x x))) := by grind
          clear b5e118218
          have b5e123801 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (k (M.op x x) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
            first
            | (have i₁ := b5e1442 x
               have i₂ := b5e44584 (M.op x x) x x
               grind)
            | exact superpose b5e44584 b5e1442
            | (have j1 := b5e44584 (M.op x x) x x
               grind)
            | exact resolve b5e1442 b5e44584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1442 b5e44584
          have b5e123952 : (k (M.op x x) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
            first
            | (have r₁ := b5e123801
               have r₂ := b5e1440
               grind)
            | exact resolve b5e123801 b5e1440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1440 b5e123801
          have b5e124732 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b5e106761 X0
               have i₂ := b5e123952
               grind)
            | exact superpose b5e123952 b5e106761
            | exact resolve b5e106761 b5e123952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106761 b5e123952
          have b5e127227 : ∀ X0 X1 : G, (M.op X1 (σ (M.op y y))) = (σ (M.op X0 (M.op x x))) := by
            intro X0 X1
            first
            | (have i₁ := b5e124732 X1
               have i₂ := b5e145 (M.op x x) x X0
               grind)
            | (have i₁ := b5e124732 X1
               have i₂ := b5e145 X0 x (M.op x x)
               grind)
            | exact superpose b5e145 b5e124732
            | exact resolve b5e124732 b5e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e145 b5e124732
          have b5e129798 : ∀ X0 X1 : G, (M.op X1 (M.op x x)) = (τ (M.op X0 (σ (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (M.op X1 (M.op x x))
               have i₂ := b5e127227 X1 X0
               grind)
            | exact superpose b5e127227 b5e14
            | exact resolve b5e14 b5e127227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e127227
          have b5e133044 : ∀ X0 : G, (M.op x x) = (M.op (τ (M.op X0 (σ (M.op y y)))) (τ (M.op X0 (σ (M.op y y))))) := by
            intro X0
            first
            | (have i₁ := b5e41 x x x
               have i₂ := b5e129798 X0 x
               grind)
            | exact superpose b5e129798 b5e41
            | exact resolve b5e41 b5e129798
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e129798
          have b5e133206 : (M.op x x) = (M.op (k (M.op x x) (M.op x x)) (k (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b5e133044 x
               have i₂ := b5e106762 x
               grind)
            | exact superpose b5e106762 b5e133044
            | exact resolve b5e133044 b5e106762
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106762 b5e133044
          have b5e133324 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b5e133206
               have i₂ := b5e118219
               grind)
            | exact superpose b5e118219 b5e133206
            | exact resolve b5e133206 b5e118219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118219 b5e133206
          have b5e134743 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1441
               have i₂ := b5e133324
               grind)
            | exact superpose b5e133324 b5e1441
            | exact resolve b5e1441 b5e133324
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1441 b5e133324
          have b5e134935 : False := by grind
          exact b5e134935
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
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
        have b6e26 : (k x y) = (τ (σ y)) := by
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
        have b6e27 : y = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e99 : y = (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
        have b6e106 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e99
             have r₂ := b6e20
             grind)
          | exact resolve b6e99 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e109 : y = (M.op x y) := by
          first
          | (have r₁ := b6e106
             have r₂ := b6e21
             grind)
          | exact resolve b6e106 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106
        have b6e111 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e12 y X0 x
             have i₂ := b6e109
             grind)
          | exact superpose b6e109 b6e12
          | exact resolve b6e12 b6e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e131 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e111 x
             have i₂ := b6e109
             grind)
          | exact superpose b6e109 b6e111
          | exact resolve b6e111 b6e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e109 b6e111
        have b6e135 : False := by grind
        exact b6e135
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b7e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X3 (M.op X4 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X2 X3 X4
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X3 (M.op X3 (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X1 (M.op X2 X0)) X3 X1
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X1 X0) X2 X2
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 (M.op X1 (M.op X2 X3))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X2 X3) X2
               have i₂ := b7e13 (M.op X2 X3) X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2
            grind
          have b7e40 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e36 X0 X1 X2 x
               have i₂ := b7e13 X0 x X0
               grind)
            | exact superpose b7e13 b7e36
            | exact resolve b7e36 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e58 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 X0
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e17
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e62 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e59
          have b7e63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e58 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e64 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e23
               grind)
            | exact resolve b7e62 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e65 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e64
            | exact resolve b7e64 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : (σ (k x y)) = (k (σ x) (σ (k x y))) := by grind
          have b7e69 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ x)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e17
            | exact resolve b7e17 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e71 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by grind
          clear b7e69
          have b7e72 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e71
            | exact resolve b7e71 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e73 : (σ (k x y)) = (σ (k x (k x y))) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e19 x (k x y)
               grind)
            | exact superpose b7e19 b7e68
            | exact resolve b7e68 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 X1 X0
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e17 X1 X1
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e17
            | (have j0 := b7e17 X1 X0
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e17 X0 X0
               have r₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b7e17 X0 X0
               have r₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b7e17 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | exact resolve b7e17 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e92 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e110 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e109 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109
          have b7e142 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e37 (M.op X3 X1) X2 X4
               have i₂ := b7e37 X1 X3 X0
               grind)
            | (have i₁ := b7e37 (M.op X0 X0) X1 X2
               have i₂ := b7e37 X0 X1 (M.op X0 X0)
               grind)
            | exact superpose b7e37 b7e37
            | exact resolve b7e37 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e172 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e142 X0 X1 x x X4
               have i₂ := b7e40 X1 x x
               grind)
            | exact superpose b7e40 b7e142
            | exact resolve b7e142 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e142
          have b7e223 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0))))) = (M.op X5 (M.op X5 (M.op X0 X0))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e34 X1 X2 (M.op X3 (M.op X4 X0)) X5 X3
               have i₂ := b7e13 X0 X3 X4
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e259 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e223 X0 X1 X2 X3 X4 x
               have i₂ := b7e13 X0 x X0
               grind)
            | exact superpose b7e13 b7e223
            | exact resolve b7e223 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e223
          have b7e343 : (k x (k x y)) = (τ (σ (k x y))) := by
            first
            | (have i₁ := b7e14 (k x (k x y))
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e14
            | exact resolve b7e14 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e344 : (k x y) = (k x (k x y)) := by
            first
            | (have i₁ := b7e343
               have i₂ := b7e14 (k x y)
               grind)
            | exact superpose b7e14 b7e343
            | exact resolve b7e343 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e343
          have b7e376 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op X3 X2) (M.op X4 (M.op X0 (M.op X0 (M.op X1 X2))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e38 X4 X4 X3 X2
               have i₂ := b7e34 X4 X3 X2 X0 X1
               grind)
            | (have i₁ := b7e38 X4 X4 X3 X2
               have i₂ := b7e34 X0 X1 X2 X4 X3
               grind)
            | exact superpose b7e34 b7e38
            | exact resolve b7e38 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e38
          have b7e441 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e344
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e344
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e344 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e344
          have b7e442 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e441
               have r₂ := b7e21
               grind)
            | exact resolve b7e441 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e441
          have b7e443 : (M.op x y) = (k x (M.op x y)) := by
            first
            | (have r₁ := b7e442
               have r₂ := b7e22
               grind)
            | exact resolve b7e442 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e442
          have b7e946 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e110 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e1062 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 (M.op X1 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e63 X1 X2 X0
               grind)
            | exact superpose b7e63 b7e13
            | (have j1 := b7e63 X1 X2 X0
               grind)
            | exact resolve b7e13 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e11267 : (k x x) = (τ (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e14
            | exact resolve b7e14 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e11299 : (σ x) = (σ (k x y)) ∨ (k x y) = (k x x) := by
            first
            | (have i₁ := b7e11267
               have i₂ := b7e14 (k x y)
               grind)
            | exact superpose b7e14 b7e11267
            | exact resolve b7e11267 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11267
          have b7e11300 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e11299
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e11299
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e11299 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11299
          have b7e11361 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e11300
               have r₂ := b7e21
               grind)
            | exact resolve b7e11300 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11300
          have b7e11362 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
            first
            | (have r₁ := b7e11361
               have r₂ := b7e22
               grind)
            | exact resolve b7e11361 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11361
          have b7e12359 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k x x) := by
            first
            | (have i₁ := b7e14 (M.op x y)
               have i₂ := b7e11362
               grind)
            | exact superpose b7e11362 b7e14
            | exact resolve b7e14 b7e11362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11362
          have b7e12396 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e12359
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e12359
            | exact resolve b7e12359 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12359
          have b7e12640 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e39 x x X0
               have i₂ := b7e1062 X0 x x
               grind)
            | exact superpose b7e1062 b7e39
            | (have j1 := b7e1062 X0 x x
               grind)
            | exact resolve b7e39 b7e1062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e1062
          have b7e15710 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e12640 x
               have i₂ := b7e12396
               grind)
            | exact superpose b7e12396 b7e12640
            | exact resolve b7e12640 b7e12396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e12396 b7e12640
          have b7e15720 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b7e15710
          have b7e17041 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 (M.op x y))))) ∨ x = (M.op x y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e259 x X1 X2 x x
               have i₂ := b7e15720
               grind)
            | exact superpose b7e15720 b7e259
            | exact resolve b7e259 b7e15720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e15720
          have b7e17057 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e17041 x x x
               have i₂ := b7e259 y x x x x
               grind)
            | exact superpose b7e259 b7e17041
            | exact resolve b7e17041 b7e259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e259 b7e17041
          have b7e17078 : x = (M.op x y) := by
            first
            | (have r₁ := b7e17057
               have r₂ := b7e22
               grind)
            | exact resolve b7e17057 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e17057
          have b7e17123 : x ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e17078
               grind)
            | exact superpose b7e17078 b7e22
            | exact resolve b7e22 b7e17078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e17128 : x = (k x x) := by
            first
            | (have i₁ := b7e443
               have i₂ := b7e17078
               grind)
            | exact superpose b7e17078 b7e443
            | exact resolve b7e443 b7e17078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e443
          have b7e17132 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e17078
               grind)
            | exact superpose b7e17078 b7e13
            | exact resolve b7e13 b7e17078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e17078
          have b7e17784 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e946 x x
               have i₂ := b7e17128
               grind)
            | exact superpose b7e17128 b7e946
            | (have j0 := b7e946 x x
               grind)
            | (have r₁ := b7e946 x x
               have r₂ := b7e17128
               grind)
            | exact resolve b7e946 b7e17128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e946 b7e17128
          have b7e17785 : x ≠ x ∨ x = (M.op x x) := by grind
          clear b7e17784
          have b7e17786 : x = (M.op x x) := by grind
          clear b7e17785
          have b7e18691 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) (M.op X1 (M.op X2 (M.op X2 x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e376 X0 x x x x
               have i₂ := b7e17786
               grind)
            | exact superpose b7e17786 b7e376
            | exact resolve b7e376 b7e17786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e376 b7e17786
          have b7e18702 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) (M.op X1 (M.op y y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e18691 X0 X1 x
               have i₂ := b7e17132 x
               grind)
            | exact superpose b7e17132 b7e18691
            | exact resolve b7e18691 b7e17132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e17132 b7e18691
          have b7e18729 : x = (M.op y y) := by
            first
            | (have i₁ := b7e18702 x x
               have i₂ := b7e172 x y (M.op x x)
               grind)
            | exact superpose b7e172 b7e18702
            | exact resolve b7e18702 b7e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e172 b7e18702
          have b7e18742 : False := by grind
          exact b7e18742
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
          have b8e80 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e1385 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e80 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e1386 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1385
               have r₂ := b8e24
               grind)
            | exact resolve b8e1385 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1385
          have b8e1387 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1386
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1386
            | exact resolve b8e1386 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1386
          have b8e1389 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1387
               grind)
            | exact superpose b8e1387 b8e20
            | exact resolve b8e20 b8e1387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1387
          have b8e1607 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1389
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1389
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1389 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1389
          have b8e1608 : y = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1607
          have b8e1610 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1608
               have r₂ := b8e21
               grind)
            | exact resolve b8e1608 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1608
          have b8e1613 : False := by grind
          exact b8e1613

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_pyy_pxx_pxy_Equation3284 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3284 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : (M.op x y) = (M.op y y) := by grind
      have b0e18 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
      have b0e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e47 (σ X0)
           grind)
        | exact superpose b0e47 b0e15
        | exact resolve b0e15 b0e47
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
      have b0e493 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e59 y
           grind)
        | exact superpose b0e59 b0e20
        | (have r₁ := b0e20
           have r₂ := b0e59 y
           grind)
        | exact resolve b0e20 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20 b0e59
      have b0e509 : False := by grind
      exact b0e509
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
        intro X0 X1 X2
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : (M.op x y) = (M.op y y) := by grind
      have b1e18 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16
        | exact resolve b1e16 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e41 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 y y
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e46 : (M.op x x) = (k x y) := by grind
      clear b1e41
      have b1e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e44 (σ X0)
           grind)
        | exact superpose b1e44 b1e15
        | exact resolve b1e15 b1e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e48 X0
           have i₂ := b1e44 X0
           grind)
        | exact superpose b1e44 b1e48
        | exact resolve b1e48 b1e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44 b1e48
      have b1e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e68 X0 X1
           have i₂ := b1e53 X1
           grind)
        | exact superpose b1e53 b1e68
        | (have j0 := b1e68 X0 X1
           grind)
        | exact resolve b1e68 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e68
      have b1e530 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 (σ X0) X1 (σ X0)
           have i₂ := b1e53 X0
           grind)
        | exact superpose b1e53 b1e10
        | exact resolve b1e10 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1482 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e73 x y
           grind)
        | exact superpose b1e73 b1e18
        | (have j1 := b1e73 x y
           grind)
        | exact resolve b1e18 b1e73
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1497 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (M.op X2 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X1) X2 (σ X0)
           have i₂ := b1e73 X0 X1
           grind)
        | exact superpose b1e73 b1e10
        | (have j1 := b1e73 X0 X1
           grind)
        | exact resolve b1e10 b1e73
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e73
      have b1e1520 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op X2 (M.op X2 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e1497 X0 X1 X2
           have i₂ := b1e53 X1
           grind)
        | exact superpose b1e53 b1e1497
        | (have j0 := b1e1497 X0 X1 X2
           grind)
        | exact resolve b1e1497 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1497
      have b1e1521 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b1e1482
           have r₂ := b1e19
           grind)
        | exact resolve b1e1482 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1482
      have b1e1554 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e1521
           have i₂ := b1e46
           grind)
        | exact superpose b1e46 b1e1521
        | exact resolve b1e1521 b1e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1521
      have b1e1571 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e1554
           have i₂ := b1e53 y
           grind)
        | exact superpose b1e53 b1e1554
        | exact resolve b1e1554 b1e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53 b1e1554
      have b1e73354 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op X0 (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e1520 x y X0
           have i₂ := b1e46
           grind)
        | exact superpose b1e46 b1e1520
        | (have j0 := b1e1520 x y x
           grind)
        | exact resolve b1e1520 b1e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46 b1e1520
      have b1e73782 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op X0 (σ (M.op x x)))) := by
        intro X0
        first
        | (have j0 := b1e73354 X0
           grind)
        | (have r₁ := b1e73354 X0
           have r₂ := b1e19
           grind)
        | exact resolve b1e73354 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19 b1e73354
      have b1e73920 : (σ (M.op y y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b1e73782 x
           have i₂ := b1e530 x x
           grind)
        | exact superpose b1e530 b1e73782
        | exact resolve b1e73782 b1e530
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e530 b1e73782
      have b1e74018 : False := by grind
      exact b1e74018
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : (M.op x y) ≠ (M.op y y) := by grind
      have b2e18 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e42 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ y) (σ y)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e45 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b2e42
      have b2e47 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e45
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e45
        | exact resolve b2e45 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45
      have b2e81 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ x)
           have i₂ := b2e47
           grind)
        | exact superpose b2e47 b2e13
        | exact resolve b2e13 b2e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47
      have b2e83 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
      clear b2e81
      have b2e84 : (σ (k x y)) = (σ (k x x)) := by
        first
        | (have i₁ := b2e83
           have i₂ := b2e15 x x
           grind)
        | exact superpose b2e15 b2e83
        | exact resolve b2e83 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e83
      have b2e85 : (σ (k x y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e84
           have i₂ := b2e44 x
           grind)
        | exact superpose b2e44 b2e84
        | exact resolve b2e84 b2e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44 b2e84
      have b2e133 : (k x y) = (τ (σ (M.op x x))) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e85
           grind)
        | exact superpose b2e85 b2e11
        | exact resolve b2e11 b2e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e85
      have b2e134 : (k x y) = (M.op x x) := by
        first
        | (have i₁ := b2e133
           have i₂ := b2e11 (M.op x x)
           grind)
        | exact superpose b2e11 b2e133
        | exact resolve b2e133 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e133
      have b2e208 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e134
           grind)
        | exact superpose b2e134 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e134
      have b2e209 : (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b2e208
           have r₂ := b2e17
           grind)
        | exact resolve b2e208 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e208
      have b2e266 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b2e10 x x x
           have i₂ := b2e209
           grind)
        | exact superpose b2e209 b2e10
        | exact resolve b2e10 b2e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e209
      have b2e268 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e266 x
           have i₂ := b2e10 y x x
           grind)
        | exact superpose b2e10 b2e266
        | exact resolve b2e266 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e266
      have b2e271 : False := by grind
      exact b2e271
    · have b3e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : (M.op x y) ≠ (M.op y y) := by grind
      have b3e18 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 X0
           have i₂ := b3e41 (σ X0)
           grind)
        | exact superpose b3e41 b3e15
        | exact resolve b3e15 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e44 X0
           have i₂ := b3e41 X0
           grind)
        | exact superpose b3e41 b3e44
        | exact resolve b3e44 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e41 b3e44
      have b3e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X0 X1
           have i₂ := b3e14 (σ X0) (σ X1)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e64 X0 X1
           have i₂ := b3e49 X1
           grind)
        | exact superpose b3e49 b3e64
        | (have j0 := b3e64 X0 X1
           grind)
        | exact resolve b3e64 b3e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e64
      have b3e1561 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e69 x y
           grind)
        | exact superpose b3e69 b3e16
        | (have j1 := b3e69 x y
           grind)
        | exact resolve b3e16 b3e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e69
      have b3e28432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b3e1561
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e1561
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e1561 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1561
      have b3e28438 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b3e28432
      have b3e28439 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have r₁ := b3e28438
           have r₂ := b3e17
           grind)
        | exact resolve b3e28438 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e28438
      have b3e28444 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e28439
           grind)
        | exact superpose b3e28439 b3e18
        | exact resolve b3e18 b3e28439
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e28439
      have b3e28521 : False := by grind
      exact b3e28521

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_y_pxx_x_pxy_Equation3284 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3284 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e22 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
      have b0e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e50 (σ X0)
           grind)
        | exact superpose b0e50 b0e17
        | exact resolve b0e17 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e57 X0
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e57
        | exact resolve b0e57 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e57
      have b0e715 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e23
           have i₂ := b0e62 y
           grind)
        | exact superpose b0e62 b0e23
        | (have r₁ := b0e23
           have r₂ := b0e62 y
           grind)
        | exact resolve b0e23 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e62
      have b0e734 : False := by grind
      exact b0e734
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y y) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) x (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e15
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e52 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e151 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e56 X0 X0 (σ y)
             have i₂ := b1e33 X0
             grind)
          | exact superpose b1e33 b1e56
          | exact resolve b1e56 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e56
        have b1e179 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k y y)) := by
          intro X0
          first
          | (have i₁ := b1e151 X0
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e151
          | exact resolve b1e151 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e151
        have b1e188 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e179 X0
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e179
          | exact resolve b1e179 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e179
        have b1e3726 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e188 (σ x)
             grind)
          | exact superpose b1e188 b1e24
          | (have r₁ := b1e24
             have r₂ := b1e188 (σ x)
             grind)
          | exact resolve b1e24 b1e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e188
        have b1e3727 : False := by grind
        exact b1e3727
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X3 (M.op X3 (M.op X0 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X1 (M.op X2 X0)) X3 X1
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e34 X0 X1 X2 x
             have i₂ := b2e12 X0 x X0
             grind)
          | exact superpose b2e12 b2e34
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e54 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : (M.op x x) = (k x y) := by grind
        clear b2e54
        have b2e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e57 (σ X0)
             grind)
          | exact superpose b2e57 b2e18
          | exact resolve b2e18 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e61 X0
             have i₂ := b2e57 X0
             grind)
          | exact superpose b2e57 b2e61
          | exact resolve b2e61 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e61
        have b2e90 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b2e459 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e37 (σ X0) X1 (σ X0)
             have i₂ := b2e68 X0
             grind)
          | exact superpose b2e68 b2e37
          | exact resolve b2e37 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1544 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e90 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e1545 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1544
             have r₂ := b2e21
             grind)
          | exact resolve b2e1544 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1544
        have b2e1546 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1545
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1545
          | exact resolve b2e1545 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1545
        have b2e1547 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1546
             have i₂ := b2e59
             grind)
          | exact superpose b2e59 b2e1546
          | exact resolve b2e1546 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e1546
        have b2e1549 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e24
             have i₂ := b2e1547
             grind)
          | exact superpose b2e1547 b2e24
          | exact resolve b2e24 b2e1547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e1557 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ (M.op x x))) (M.op X0 (σ (M.op x x)))) := by
          intro X0
          first
          | (have i₁ := b2e37 (σ y) x (σ x)
             have i₂ := b2e1547
             grind)
          | exact superpose b2e1547 b2e37
          | exact resolve b2e37 b2e1547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e1547
        have b2e1562 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1557 x
             have i₂ := b2e459 x x
             grind)
          | exact superpose b2e459 b2e1557
          | exact resolve b2e1557 b2e459
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e459 b2e1557
        have b2e1572 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1562
             have i₂ := b2e68 y
             grind)
          | exact superpose b2e68 b2e1562
          | exact resolve b2e1562 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e1562
        have b2e1579 : False := by grind
        exact b2e1579
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e32 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e12 x x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 y X0 X0
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e47 : (M.op y y) ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e38 x
             grind)
          | exact superpose b3e38 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e38 x
             grind)
          | exact resolve b3e20 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e48 : False := by grind
        exact b3e48
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b4e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e13 x x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 X0
               have i₂ := b4e29 X0
               grind)
            | exact superpose b4e29 b4e13
            | exact resolve b4e13 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e44 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e36 x
               grind)
            | exact superpose b4e36 b4e21
            | (have r₁ := b4e21
               have r₂ := b4e36 x
               grind)
            | exact resolve b4e21 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e45 : False := by grind
          exact b4e45
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b5e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e13 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 X0
               have i₂ := b5e29 X0
               grind)
            | exact superpose b5e29 b5e13
            | exact resolve b5e13 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e43 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e35 x
               grind)
            | exact superpose b5e35 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e35 x
               grind)
            | exact resolve b5e21 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e44 : False := by grind
          exact b5e44
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e55
        have b6e60 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e116 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e15
          | exact resolve b6e15 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e118 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e116
        have b6e119 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e118
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e118
          | exact resolve b6e118 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e118
        have b6e120 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e119
             have i₂ := b6e57 x
             grind)
          | exact superpose b6e57 b6e119
          | exact resolve b6e119 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57 b6e119
        have b6e148 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e120
             grind)
          | exact superpose b6e120 b6e13
          | exact resolve b6e13 b6e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e149 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e148
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e148
          | exact resolve b6e148 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e148
        have b6e209 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e149
             grind)
          | exact superpose b6e149 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e210 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e209
             have r₂ := b6e20
             grind)
          | exact resolve b6e209 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e209
        have b6e212 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e210
             have r₂ := b6e21
             grind)
          | exact resolve b6e210 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e210
        have b6e307 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b6e12 x x x
             have i₂ := b6e212
             grind)
          | exact superpose b6e212 b6e12
          | exact resolve b6e12 b6e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e212
        have b6e309 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e307 x
             have i₂ := b6e12 y x x
             grind)
          | exact superpose b6e12 b6e307
          | exact resolve b6e307 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e307
        have b6e312 : False := by grind
        exact b6e312
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e42 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : (σ y) = (k (σ x) (σ x)) := by grind
          clear b7e42
          have b7e49 : (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e46 x
               grind)
            | exact superpose b7e46 b7e49
            | exact resolve b7e49 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46 b7e49
          have b7e99 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e100 : y = (M.op x x) := by
            first
            | (have i₁ := b7e99
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e99
            | exact resolve b7e99 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e103 : False := by grind
          exact b7e103
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e76 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e1529 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e76 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e1530 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1529
               have r₂ := b8e23
               grind)
            | exact resolve b8e1529 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1529
          have b8e1531 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1530
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1530
            | exact resolve b8e1530 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1530
          have b8e1533 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1531
               grind)
            | exact superpose b8e1531 b8e20
            | exact resolve b8e20 b8e1531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1531
          have b8e1754 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e1533
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1533
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1533 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1533
          have b8e1755 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e1754
          have b8e1757 : y = (M.op x x) := by
            first
            | (have r₁ := b8e1755
               have r₂ := b8e21
               grind)
            | exact resolve b8e1755 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1755
          have b8e1760 : False := by grind
          exact b8e1760

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_y_pxx_y_pxy_Equation3284 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3284 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e22 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
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
      have b0e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e50 (σ X0)
           grind)
        | exact superpose b0e50 b0e17
        | exact resolve b0e17 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e57 X0
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e57
        | exact resolve b0e57 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e57
      have b0e608 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e23
           have i₂ := b0e62 y
           grind)
        | exact superpose b0e62 b0e23
        | (have r₁ := b0e23
           have r₂ := b0e62 y
           grind)
        | exact resolve b0e23 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e62
      have b0e627 : False := by grind
      exact b0e627
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op y y) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) x (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e15
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e52 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e175 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e56 X0 X0 (σ y)
             have i₂ := b1e33 X0
             grind)
          | exact superpose b1e33 b1e56
          | exact resolve b1e56 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e56
        have b1e202 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k y y)) := by
          intro X0
          first
          | (have i₁ := b1e175 X0
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e175
          | exact resolve b1e175 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e175
        have b1e212 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e202 X0
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e202
          | exact resolve b1e202 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e202
        have b1e3711 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e212 (σ x)
             grind)
          | exact superpose b1e212 b1e24
          | (have r₁ := b1e24
             have r₂ := b1e212 (σ x)
             grind)
          | exact resolve b1e24 b1e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e212
        have b1e3712 : False := by grind
        exact b1e3712
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X3 (M.op X3 (M.op X0 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X1 (M.op X2 X0)) X3 X1
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e34 X0 X1 X2 x
             have i₂ := b2e12 X0 x X0
             grind)
          | exact superpose b2e12 b2e34
          | exact resolve b2e34 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e54 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : (M.op x x) = (k x y) := by grind
        clear b2e54
        have b2e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e57 (σ X0)
             grind)
          | exact superpose b2e57 b2e18
          | exact resolve b2e18 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e61 X0
             have i₂ := b2e57 X0
             grind)
          | exact superpose b2e57 b2e61
          | exact resolve b2e61 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e61
        have b2e90 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b2e574 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 (σ (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e37 (σ X0) X1 (σ X0)
             have i₂ := b2e68 X0
             grind)
          | exact superpose b2e68 b2e37
          | exact resolve b2e37 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1362 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e90 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e1363 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1362
             have r₂ := b2e21
             grind)
          | exact resolve b2e1362 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1362
        have b2e1364 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1363
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1363
          | exact resolve b2e1363 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1363
        have b2e1365 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1364
             have i₂ := b2e59
             grind)
          | exact superpose b2e59 b2e1364
          | exact resolve b2e1364 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e1364
        have b2e1367 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e24
             have i₂ := b2e1365
             grind)
          | exact superpose b2e1365 b2e24
          | exact resolve b2e24 b2e1365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e1375 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ (M.op x x))) (M.op X0 (σ (M.op x x)))) := by
          intro X0
          first
          | (have i₁ := b2e37 (σ y) x (σ x)
             have i₂ := b2e1365
             grind)
          | exact superpose b2e1365 b2e37
          | exact resolve b2e37 b2e1365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e1365
        have b2e1380 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1375 x
             have i₂ := b2e574 x x
             grind)
          | exact superpose b2e574 b2e1375
          | exact resolve b2e1375 b2e574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e574 b2e1375
        have b2e1390 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1380
             have i₂ := b2e68 y
             grind)
          | exact superpose b2e68 b2e1380
          | exact resolve b2e1380 b2e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68 b2e1380
        have b2e1397 : False := by grind
        exact b2e1397
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e32 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e12 x x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e12 y X0 X0
             have i₂ := b3e32 X0
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e47 : (M.op y y) ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e38 x
             grind)
          | exact superpose b3e38 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e38 x
             grind)
          | exact resolve b3e20 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e48 : False := by grind
        exact b3e48
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b4e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e13 x x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 X0
               have i₂ := b4e29 X0
               grind)
            | exact superpose b4e29 b4e13
            | exact resolve b4e13 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e44 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e36 x
               grind)
            | exact superpose b4e36 b4e21
            | (have r₁ := b4e21
               have r₂ := b4e36 x
               grind)
            | exact resolve b4e21 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e45 : False := by grind
          exact b4e45
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b5e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e13 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 X0
               have i₂ := b5e29 X0
               grind)
            | exact superpose b5e29 b5e13
            | exact resolve b5e13 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e43 : (M.op y y) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e35 x
               grind)
            | exact superpose b5e35 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e35 x
               grind)
            | exact resolve b5e21 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e44 : False := by grind
          exact b5e44
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e55
        have b6e60 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e116 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e15
          | exact resolve b6e15 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e118 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e116
        have b6e119 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e118
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e118
          | exact resolve b6e118 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e118
        have b6e120 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e119
             have i₂ := b6e57 x
             grind)
          | exact superpose b6e57 b6e119
          | exact resolve b6e119 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57 b6e119
        have b6e217 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e120
             grind)
          | exact superpose b6e120 b6e13
          | exact resolve b6e13 b6e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e218 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e217
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e217
          | exact resolve b6e217 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e217
        have b6e310 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e218
             grind)
          | exact superpose b6e218 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e218
        have b6e311 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e310
             have r₂ := b6e20
             grind)
          | exact resolve b6e310 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e310
        have b6e313 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e311
             have r₂ := b6e21
             grind)
          | exact resolve b6e311 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e311
        have b6e419 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b6e12 x x x
             have i₂ := b6e313
             grind)
          | exact superpose b6e313 b6e12
          | exact resolve b6e12 b6e313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e313
        have b6e430 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e419 x
             have i₂ := b6e12 y x x
             grind)
          | exact superpose b6e12 b6e419
          | exact resolve b6e419 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e419
        have b6e434 : False := by grind
        exact b6e434
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e42 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : (σ y) = (k (σ x) (σ x)) := by grind
          clear b7e42
          have b7e49 : (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e46 x
               grind)
            | exact superpose b7e46 b7e49
            | exact resolve b7e49 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46 b7e49
          have b7e99 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e100 : y = (M.op x x) := by
            first
            | (have i₁ := b7e99
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e99
            | exact resolve b7e99 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e103 : False := by grind
          exact b7e103
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e76 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e1348 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e76 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e1349 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1348
               have r₂ := b8e23
               grind)
            | exact resolve b8e1348 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1348
          have b8e1350 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1349
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1349
            | exact resolve b8e1349 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1349
          have b8e1352 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1350
               grind)
            | exact superpose b8e1350 b8e20
            | exact resolve b8e20 b8e1350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1350
          have b8e1566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e1352
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1352
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1352 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1352
          have b8e1567 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e1566
          have b8e1569 : y = (M.op x x) := by
            first
            | (have r₁ := b8e1567
               have r₂ := b8e21
               grind)
            | exact resolve b8e1567 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1567
          have b8e1572 : False := by grind
          exact b8e1572

/-- `Equation329`: `x ◇ y = x ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pxy_Equation329 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law329 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law329.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e29
      have b0e79 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e30
      have b0e83 : False := by grind
      exact b0e83
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y y)) := by
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
          have b4e29 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e26 X0
               have i₂ := b4e13 X0 y y
               grind)
            | exact superpose b4e13 b4e26
            | exact resolve b4e26 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e33
          have b4e45 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e45 X0
               have i₂ := b4e13 X0 (σ y) (σ y)
               grind)
            | exact superpose b4e13 b4e45
            | exact resolve b4e45 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e110 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e46 (σ x)
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e46
            | exact resolve b4e46 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e46
          have b4e114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e110
               have i₂ := b4e29 x
               grind)
            | exact superpose b4e29 b4e110
            | exact resolve b4e110 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e110
          have b4e116 : False := by grind
          exact b4e116
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y y)) := by
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
          have b5e29 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e26 X0
               have i₂ := b5e13 X0 y y
               grind)
            | exact superpose b5e13 b5e26
            | exact resolve b5e26 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e33
          have b5e70 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e17 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e70 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e82 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e78 X0 X1
               have i₂ := b5e34 X1
               grind)
            | exact superpose b5e34 b5e78
            | (have j0 := b5e78 X0 X1
               grind)
            | exact resolve b5e78 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e498 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e83 y x
               grind)
            | exact superpose b5e83 b5e20
            | (have j1 := b5e83 y x
               grind)
            | exact resolve b5e20 b5e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e83
          have b5e539 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e498
               have r₂ := b5e23
               grind)
            | exact resolve b5e498 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e498
          have b5e571 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e539
               have i₂ := b5e29 x
               grind)
            | exact superpose b5e29 b5e539
            | exact resolve b5e539 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29 b5e539
          have b5e572 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
          clear b5e571
          have b5e605 : (M.op (σ y) (σ y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e572
               grind)
            | exact superpose b5e572 b5e24
            | exact resolve b5e24 b5e572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e606 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (k y x))) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ x) (σ y)
               have i₂ := b5e572
               grind)
            | exact superpose b5e572 b5e13
            | exact resolve b5e13 b5e572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e572
          have b5e619 : (σ (M.op y y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e605
               have i₂ := b5e34 y
               grind)
            | exact superpose b5e34 b5e605
            | exact resolve b5e605 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e605
          have b5e755 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e619
               have i₂ := b5e82 x y
               grind)
            | exact superpose b5e82 b5e619
            | (have j1 := b5e82 x y
               grind)
            | (have r₁ := b5e619
               have r₂ := b5e82 (σ (M.op y y)) (σ (k y x))
               grind)
            | (have r₁ := b5e619
               have r₂ := b5e82 (σ (k y x)) (σ (M.op y y))
               grind)
            | exact resolve b5e619 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82 b5e619
          have b5e757 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by
            first
            | (have r₁ := b5e755
               have r₂ := b5e21
               grind)
            | exact resolve b5e755 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e755
          have b5e758 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b5e757
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e757
            | exact resolve b5e757 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e757
          have b5e759 : y = (k y x) := by grind
          clear b5e758
          have b5e1195 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e606 X0
               have i₂ := b5e759
               grind)
            | exact superpose b5e759 b5e606
            | exact resolve b5e606 b5e759
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e606 b5e759
          have b5e1500 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1195 (σ y)
               grind)
            | exact superpose b5e1195 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1195 (σ y)
               grind)
            | exact resolve b5e24 b5e1195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1195
          have b5e1504 : False := by grind
          exact b5e1504
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e31
          have b7e34 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) := by
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
          have b7e35 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e34 X0
               have i₂ := b7e13 X0 (σ y) (σ y)
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e40 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
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
          have b7e82 : x = (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
          have b7e83 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e82
               have r₂ := b7e22
               grind)
            | exact resolve b7e82 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e85 : x = (M.op x y) := by
            first
            | (have r₁ := b7e83
               have r₂ := b7e21
               grind)
            | exact resolve b7e83 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e95 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e13
            | exact resolve b7e13 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e121 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e35 (σ x)
               have i₂ := b7e32 x
               grind)
            | exact superpose b7e32 b7e35
            | exact resolve b7e35 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e35
          have b7e125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e121
               have i₂ := b7e95 x
               grind)
            | exact superpose b7e95 b7e121
            | exact resolve b7e121 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95 b7e121
          have b7e129 : False := by grind
          exact b7e129
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e31
          have b8e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e66 X0 X1
               have i₂ := b8e32 X1
               grind)
            | exact superpose b8e32 b8e66
            | (have j0 := b8e66 X0 X1
               grind)
            | exact resolve b8e66 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e431 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e70 x y
               grind)
            | exact superpose b8e70 b8e20
            | (have j1 := b8e70 x y
               grind)
            | exact resolve b8e20 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e491 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e431
               have r₂ := b8e23
               grind)
            | exact resolve b8e431 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e431
          have b8e2009 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e491
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e491
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e491
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e491
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e491 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e491
          have b8e2010 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by grind
          clear b8e2009
          have b8e2015 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have r₁ := b8e2010
               have r₂ := b8e22
               grind)
            | exact resolve b8e2010 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2010
          have b8e2020 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e2015
               have r₂ := b8e21
               grind)
            | exact resolve b8e2015 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2015
          have b8e2025 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e2020
               grind)
            | exact superpose b8e2020 b8e24
            | exact resolve b8e24 b8e2020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2020
          have b8e2054 : False := by grind
          exact b8e2054

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxx_pxx_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e43 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : (M.op x x) = (k x y) := by grind
      clear b0e44
      have b0e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e43
      have b0e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
      have b0e53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e52
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e52
        | exact resolve b0e52 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e52
      have b0e54 : False := by grind
      exact b0e54
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e27 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b1e12 y x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e27 x
             have i₂ := b1e12 x x x
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e52
        have b1e61 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
        have b1e62 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e61
          | exact resolve b1e61 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e61
        have b1e63 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e32
             grind)
          | exact superpose b1e32 b1e62
          | exact resolve b1e62 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e62
        have b1e64 : False := by grind
        exact b1e64
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e55 : (M.op x x) = (k x y) := by grind
        clear b2e48
        have b2e90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e16 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e100 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e109 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e90 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e91 X0 X1
             have j1 := b2e15 X1 X0
             grind)
          | (have r₁ := b2e91 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | (have r₁ := b2e91 X1 X0
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e91 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e117 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e109 X0 X1
             have j1 := b2e15 X1 X0
             grind)
          | (have r₁ := b2e109 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | (have r₁ := b2e109 X1 X0
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e109 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109
        have b2e123 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e117 X0 X1
             have j1 := b2e116 X0 X1
             grind)
          | (have r₁ := b2e117 X0 X1
             have r₂ := b2e116 X0 X1
             grind)
          | (have r₁ := b2e117 X1 X0
             have r₂ := b2e116 X0 X1
             grind)
          | exact resolve b2e117 b2e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116 b2e117
        have b2e370 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e123 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123
        have b2e6118 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e100 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e6119 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j1 := b2e370 (σ x) (σ y)
             grind)
          | (have r₁ := b2e6118
             have r₂ := b2e370 (σ x) (σ y)
             grind)
          | exact resolve b2e6118 b2e370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e370 b2e6118
        have b2e6121 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e6119
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e6119
          | exact resolve b2e6119 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6119
        have b2e6123 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e6121
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e6121
          | exact resolve b2e6121 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e6121
        have b2e6125 : False := by grind
        exact b2e6125
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b3e44 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ x)))) := by
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
        have b3e45 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e44 x
             have i₂ := b3e12 (σ x) (σ x) x
             grind)
          | exact superpose b3e12 b3e44
          | exact resolve b3e44 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e182 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | exact resolve b3e15 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e184 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
        clear b3e182
        have b3e186 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e184
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e184
          | exact resolve b3e184 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e184
        have b3e192 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e186
             have i₂ := b3e60 y
             grind)
          | exact superpose b3e60 b3e186
          | exact resolve b3e186 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e186
        have b3e197 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e192
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e192
          | exact resolve b3e192 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e192
        have b3e200 : False := by grind
        exact b3e200
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e74 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e72
          have b4e77 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e74
            | exact resolve b4e74 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e79 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e73 y
               grind)
            | exact superpose b4e73 b4e77
            | exact resolve b4e77 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73 b4e77
          have b4e80 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e79
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e79
            | exact resolve b4e79 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e81 : False := by grind
          exact b4e81
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e70 (σ X0)
               grind)
            | exact superpose b5e70 b5e19
            | exact resolve b5e19 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e75 X0
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e75
            | exact resolve b5e75 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e75
          have b5e92 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e96 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e92 X0
               have j1 := b5e16 X0 y
               grind)
            | (have r₁ := b5e92 X0
               have r₂ := b5e16 X0 y
               grind)
            | (have r₁ := b5e92 y
               have r₂ := b5e16 y y
               grind)
            | exact resolve b5e92 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92
          have b5e131 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X1 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e16 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e141 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e131 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e159 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e132 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e132 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | (have r₁ := b5e132 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e132 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e160 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e151 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e151 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | (have r₁ := b5e151 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e151 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e151
          have b5e166 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e160 X0 X1
               have j1 := b5e159 X0 X1
               grind)
            | (have r₁ := b5e160 X0 X1
               have r₂ := b5e159 X0 X1
               grind)
            | (have r₁ := b5e160 X1 X0
               have r₂ := b5e159 X0 X1
               grind)
            | exact resolve b5e160 b5e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e159 b5e160
          have b5e490 : (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e96 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e551 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e166 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e166
          have b5e8706 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e141 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e141
          have b5e8707 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b5e551 (σ x) (σ y)
               grind)
            | (have r₁ := b5e8706
               have r₂ := b5e551 (σ x) (σ y)
               grind)
            | exact resolve b5e8706 b5e551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e551 b5e8706
          have b5e8709 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e8707
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e8707
            | exact resolve b5e8707 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8707
          have b5e8711 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e8709
               have i₂ := b5e490
               grind)
            | exact superpose b5e490 b5e8709
            | exact resolve b5e8709 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e490 b5e8709
          have b5e8714 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e8711
               grind)
            | exact superpose b5e8711 b5e23
            | exact resolve b5e23 b5e8711
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8711
          have b5e8746 : False := by grind
          exact b5e8746
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
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
        have b6e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e56
        have b6e60 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e78 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e23
          | exact resolve b6e23 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e60
        have b6e147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e78
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e78 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e148 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e147
        have b6e149 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e148
             have r₂ := b6e20
             grind)
          | exact resolve b6e148 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e148
        have b6e150 : False := by grind
        exact b6e150
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e69 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e69
          have b7e73 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e71
            | exact resolve b7e71 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e74 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e70 y
               grind)
            | exact superpose b7e70 b7e73
            | exact resolve b7e73 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e70 (σ X0)
               grind)
            | exact superpose b7e70 b7e19
            | exact resolve b7e19 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e76 X0
               have i₂ := b7e70 X0
               grind)
            | exact superpose b7e70 b7e76
            | exact resolve b7e76 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e76
          have b7e94 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e96 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e94 X0
               have j1 := b7e16 X0 (σ y)
               grind)
            | (have r₁ := b7e94 X0
               have r₂ := b7e16 X0 (σ y)
               grind)
            | (have r₁ := b7e94 (σ y)
               have r₂ := b7e16 (σ y) (σ y)
               grind)
            | exact resolve b7e94 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e98 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e96 X0
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e96
            | (have j0 := b7e96 X0
               grind)
            | exact resolve b7e96 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e1065 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e98 (σ x)
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e98
            | (have j0 := b7e98 (σ x)
               grind)
            | (have r₁ := b7e98 (σ x)
               have r₂ := b7e74
               grind)
            | exact resolve b7e98 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e98
          have b7e1068 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e1065
          have b7e1070 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1068
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e1068
            | exact resolve b7e1068 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1068
          have b7e1076 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1070
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e1070
            | exact resolve b7e1070 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e1070
          have b7e1094 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1076
               grind)
            | exact superpose b7e1076 b7e14
            | exact resolve b7e14 b7e1076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1076
          have b7e1095 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e1094
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e1094
            | exact resolve b7e1094 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1094
          have b7e1142 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e1095
               grind)
            | exact superpose b7e1095 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e1095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1095
          have b7e1143 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b7e1142
          have b7e1145 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e1143
               have r₂ := b7e21
               grind)
            | exact resolve b7e1143 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1143
          have b7e1150 : False := by grind
          exact b7e1150
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e121 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (M.op X2 (M.op X0 X0))) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X0 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e140 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e143 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e123 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e151 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e124 X0 X1
               have j1 := b8e16 X1 X0
               grind)
            | (have r₁ := b8e124 X1 X1
               have r₂ := b8e16 X1 X1
               grind)
            | (have r₁ := b8e124 X1 X0
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e124 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e152 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               have j1 := b8e16 X1 X0
               grind)
            | (have r₁ := b8e143 X1 X1
               have r₂ := b8e16 X1 X1
               grind)
            | (have r₁ := b8e143 X1 X0
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e143 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e153 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e121 X0 X1 x
               have i₂ := b8e13 X0 X0 x
               grind)
            | exact superpose b8e13 b8e121
            | (have j0 := b8e121 X0 X1 x
               grind)
            | exact resolve b8e121 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e158 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e152 X0 X1
               have j1 := b8e151 X0 X1
               grind)
            | (have r₁ := b8e152 X0 X1
               have r₂ := b8e151 X0 X1
               grind)
            | (have r₁ := b8e152 X1 X0
               have r₂ := b8e151 X0 X1
               grind)
            | exact resolve b8e152 b8e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151 b8e152
          have b8e159 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e153 X0 X1
               have j1 := b8e140 X0 X1
               grind)
            | (have r₁ := b8e153 X0 X1
               have r₂ := b8e140 X0 X1
               grind)
            | (have r₁ := b8e153 X1 X0
               have r₂ := b8e140 X0 X1
               grind)
            | (have r₁ := b8e153 X1 X1
               have r₂ := b8e140 X1 X1
               grind)
            | exact resolve b8e153 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140 b8e153
          have b8e422 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e158 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158
          have b8e6415 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e133 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e6416 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b8e422 (σ x) (σ y)
               grind)
            | (have r₁ := b8e6415
               have r₂ := b8e422 (σ x) (σ y)
               grind)
            | exact resolve b8e6415 b8e422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e422 b8e6415
          have b8e6418 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e6416
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e6416
            | exact resolve b8e6416 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6416
          have b8e6425 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6418
               grind)
            | exact superpose b8e6418 b8e20
            | exact resolve b8e20 b8e6418
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6418
          have b8e6552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e6425
               have i₂ := b8e159 x y
               grind)
            | exact superpose b8e159 b8e6425
            | (have j1 := b8e159 x y
               grind)
            | exact resolve b8e6425 b8e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159 b8e6425
          have b8e6553 : (M.op x y) = (M.op y y) := by grind
          clear b8e6552
          have b8e6557 : False := by grind
          exact b8e6557
