import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4535`: `x ◇ (y ◇ z) = (y ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4535 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4535 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4535.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x y) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (σ y) ≠ (σ y) := by
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
    · have b1e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
        intro X0 X1 X2 X3
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op x y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : y ≠ y ∨ x = (k x y) := by
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
      have b1e21 : x = (k x y) := by grind
      clear b1e20
      have b1e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e24 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x y X1
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e25 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b1e10 X3 X2 (M.op X0 x) X5
           have i₂ := b1e10 X2 X0 x X1
           grind)
        | (have i₁ := b1e10 X0 (M.op X1 X3) X0 X3
           have i₂ := b1e10 X0 X1 X2 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b1e10 X2 X0 x X4
           have i₂ := b1e10 X2 X0 x X1
           grind)
        | (have i₁ := b1e10 (M.op X1 x) X1 X2 x
           have i₂ := b1e10 (M.op X1 X2) X1 X2 x
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e29 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x X1 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e10 X3 X2 X4 (M.op X0 x)
           have i₂ := b1e10 X2 X0 x X1
           grind)
        | (have i₁ := b1e10 X0 (M.op X1 X3) X2 X0
           have i₂ := b1e10 X0 X1 X2 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 X1 X2 x
           have i₂ := b1e10 X0 X1 X3 x
           grind)
        | (have i₁ := b1e10 (M.op X1 X2) X1 X2 X3
           have i₂ := b1e10 (M.op X1 X3) X1 X2 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X0 X3) ∨ (k X2 (M.op X0 X3)) = X2 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e13 X2 (M.op X0 X3)
           have i₂ := b1e10 X2 X0 X3 X1
           grind)
        | (have i₁ := b1e13 (M.op X1 X3) X0
           have i₂ := b1e10 X0 X1 X2 X3
           grind)
        | exact superpose b1e10 b1e13
        | (have j0 := b1e13 X2 (M.op X0 X3)
           grind)
        | exact resolve b1e13 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e24 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e24
        | exact resolve b1e24 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
      have b1e61 : y = (M.op y x) := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e36 x
           grind)
        | exact superpose b1e36 b1e17
        | exact resolve b1e17 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e85 : ∀ X0 X1 : G, (M.op y X0) = (M.op X0 (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 y X1 x
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e10
        | exact resolve b1e10 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e86 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op y X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 y x X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e10
        | exact resolve b1e10 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e89 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e22 X1 X0
           have i₂ := b1e14 (τ X1) X0
           grind)
        | exact superpose b1e14 b1e22
        | (have j1 := b1e14 (τ X1) X0
           grind)
        | exact resolve b1e22 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e92 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e11
        | exact resolve b1e11 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e94 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e23 X0 X1
           have i₂ := b1e14 X1 (τ X0)
           grind)
        | exact superpose b1e14 b1e23
        | (have j1 := b1e14 X1 (τ X0)
           grind)
        | exact resolve b1e23 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e23 X1 X0
           grind)
        | exact superpose b1e23 b1e11
        | exact resolve b1e11 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e148 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e27 X0 X1 X2 y
           have i₂ := b1e36 X0
           grind)
        | (have i₁ := b1e27 y X1 X2 X0
           have i₂ := b1e36 X0
           grind)
        | exact superpose b1e36 b1e27
        | exact resolve b1e27 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e178 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X2 X5) (M.op X0 X4)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e10 (M.op X0 X4) X2 X3 X5
           have i₂ := b1e27 X0 X4 (M.op X2 X3) X1
           grind)
        | (have i₁ := b1e10 (M.op X0 X4) X2 X3 X5
           have i₂ := b1e27 X0 X1 (M.op X2 X3) X4
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e191 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e148 X0 X1 X2
           have i₂ := b1e86 X2 X0
           grind)
        | exact superpose b1e86 b1e148
        | exact resolve b1e148 b1e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e148
      have b1e271 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e32 X1 X0 X2 y
           have i₂ := b1e36 X0
           grind)
        | (have i₁ := b1e32 X0 y X2 X0
           have i₂ := b1e36 X0
           grind)
        | exact superpose b1e36 b1e32
        | exact resolve b1e32 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e336 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op y X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e271 X0 X1 X2
           have i₂ := b1e85 X1 X0
           grind)
        | exact superpose b1e85 b1e271
        | exact resolve b1e271 b1e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e85 b1e271
      have b1e501 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (M.op X3 X4) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e32 X2 (M.op X3 X4) X0 X5
           have i₂ := b1e25 X3 X4 X0 X2 X1
           grind)
        | (have i₁ := b1e32 (M.op X2 X5) X1 X2 X3
           have i₂ := b1e25 X0 X1 X2 (M.op X1 X2) X5
           grind)
        | exact superpose b1e25 b1e32
        | exact resolve b1e32 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32
      have b1e505 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X3 X4) X0) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e13 X2 (M.op (M.op X3 X4) X0)
           have i₂ := b1e25 X3 X4 X0 X2 X1
           grind)
        | (have i₁ := b1e13 (M.op X2 x) X3
           have i₂ := b1e25 X0 X1 X2 X3 x
           grind)
        | exact superpose b1e25 b1e13
        | (have j0 := b1e13 X2 (M.op (M.op X3 X4) X0)
           grind)
        | (have r₁ := b1e13 X3 (M.op (M.op X3 x) X3)
           have r₂ := b1e25 X3 x X3 X3 x
           grind)
        | exact resolve b1e13 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e530 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X0 y) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e505 X0 X1 X2 X3 X4
           have i₂ := b1e191 X3 X4 X0
           grind)
        | exact superpose b1e191 b1e505
        | (have j0 := b1e505 X0 X1 X2 X3 X4
           grind)
        | (have r₁ := b1e505 y X1 (M.op X3 X4) X3 X4
           have r₂ := b1e191 y X1 (M.op X3 X4)
           grind)
        | exact resolve b1e505 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e505
      have b1e532 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e501 X0 X1 X2 x x x
           have i₂ := b1e336 (M.op x x) X2 x
           grind)
        | exact superpose b1e336 b1e501
        | exact resolve b1e501 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e501
      have b1e586 : ∀ X0 X2 X3 X4 : G, (M.op X0 y) ≠ (M.op X2 y) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b1e530 X0 x X2 X3 X4
           have i₂ := b1e191 X0 x X2
           grind)
        | exact superpose b1e191 b1e530
        | (have j0 := b1e530 X0 x X2 X3 X4
           grind)
        | (have r₁ := b1e530 X2 x X2 X3 X4
           have r₂ := b1e191 X2 x X2
           grind)
        | exact resolve b1e530 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e530
      have b1e620 : ∀ X0 X2 : G, (M.op X0 y) ≠ (M.op X2 y) ∨ (k X2 (M.op X0 y)) = X2 := by
        intro X0 X2
        first
        | (have i₁ := b1e586 X0 X2 x x
           have i₂ := b1e191 x x X0
           grind)
        | exact superpose b1e191 b1e586
        | (have j0 := b1e586 X0 X2 x x
           grind)
        | (have r₁ := b1e586 (M.op X0 x) y x x
           have r₂ := b1e191 X0 x y
           grind)
        | (have r₁ := b1e586 y (M.op X0 x) x x
           have r₂ := b1e191 X0 x y
           grind)
        | exact resolve b1e586 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e586
      have b1e831 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op X3 X4) X5) X0) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e27 (M.op X3 X4) X5 X0 X1
           have i₂ := b1e30 X3 X4 X1 X0 X2
           grind)
        | (have i₁ := b1e27 X0 X1 (M.op X2 X4) X4
           have i₂ := b1e30 X0 X1 X2 (M.op X0 X4) X4
           grind)
        | exact superpose b1e30 b1e27
        | exact resolve b1e27 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27 b1e30
      have b1e865 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e831 X0 X1 X2 x x x
           have i₂ := b1e191 (M.op x x) x X0
           grind)
        | exact superpose b1e191 b1e831
        | exact resolve b1e831 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e831
      have b1e4053 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e51 X0 X1
           have i₂ := b1e51 X1 X0
           grind)
        | exact superpose b1e51 b1e51
        | (have j0 := b1e51 X0 X1
           have j1 := b1e51 X0 X1
           grind)
        | exact resolve b1e51 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4081 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e51 y x
           grind)
        | exact superpose b1e51 b1e18
        | (have j1 := b1e51 y x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e51 y x
           grind)
        | exact resolve b1e18 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4084 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e51 X0 X1
           grind)
        | exact superpose b1e51 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e51 X0 X1
           grind)
        | (have r₁ := b1e13 (σ X1) (σ X0)
           have r₂ := b1e51 X0 X1
           grind)
        | exact resolve b1e13 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4101 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) X3) ≠ (M.op (σ X0) X2) ∨ (k X2 (M.op (σ X1) X3)) = X2 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e34 (σ X1) (σ X0) X2 X3
           have i₂ := b1e51 X0 X1
           grind)
        | exact superpose b1e51 b1e34
        | (have j0 := b1e34 (σ X1) X1 X2 X3
           have j1 := b1e51 X0 X1
           grind)
        | exact resolve b1e34 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e4108 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b1e51 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e4109 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e4084 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4084
      have b1e4110 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
      clear b1e4081
      have b1e4128 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e4109 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e4109
        | (have j0 := b1e4109 X0 X1
           grind)
        | exact resolve b1e4109 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4109
      have b1e4131 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e4110
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e4110
        | exact resolve b1e4110 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e4110
      have b1e4188 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b1e13 (σ y) (σ x)
           have i₂ := b1e4131
           grind)
        | exact superpose b1e4131 b1e13
        | (have j0 := b1e13 (σ y) (σ x)
           grind)
        | (have r₁ := b1e13 (σ y) (σ x)
           have r₂ := b1e4131
           grind)
        | exact resolve b1e13 b1e4131
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4207 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e532 (σ y) (σ x) X0
           have i₂ := b1e4131
           grind)
        | exact superpose b1e4131 b1e532
        | exact resolve b1e532 b1e4131
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4208 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e865 X0 (σ y) (σ x)
           have i₂ := b1e4131
           grind)
        | exact superpose b1e4131 b1e865
        | exact resolve b1e865 b1e4131
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e865
      have b1e4209 : (σ y) = (k (σ y) (σ x)) := by grind
      clear b1e4188
      have b1e4226 : (σ y) = (σ (k y x)) := by
        first
        | (have i₁ := b1e4209
           have i₂ := b1e15 y x
           grind)
        | exact superpose b1e15 b1e4209
        | exact resolve b1e4209 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4209
      have b1e4237 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e92 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e92
        | exact resolve b1e92 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4264 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e99 X1 X0
           have i₂ := b1e14 (σ X1) X0
           grind)
        | exact superpose b1e14 b1e99
        | (have j1 := b1e14 (σ X1) X0
           grind)
        | exact resolve b1e99 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4507 : (σ y) ≠ (M.op y (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e4207 (σ y)
           grind)
        | exact superpose b1e4207 b1e18
        | exact resolve b1e18 b1e4207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e5895 : (σ x) = (M.op (σ y) y) := by
        first
        | (have i₁ := b1e4131
           have i₂ := b1e4208 (σ y)
           grind)
        | exact superpose b1e4208 b1e4131
        | exact resolve b1e4131 b1e4208
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4131 b1e4208
      have b1e5901 : (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e5895
           have i₂ := b1e36 (σ y)
           grind)
        | exact superpose b1e36 b1e5895
        | exact resolve b1e5895 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5895
      have b1e6018 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e4507
           have i₂ := b1e5901
           grind)
        | exact superpose b1e5901 b1e4507
        | exact resolve b1e4507 b1e5901
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4507
      have b1e6365 : ∀ X0 : G, (k X0 (M.op X0 y)) = X0 := by
        intro X0
        first
        | (have j0 := b1e620 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e620
      have b1e6394 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e6365 (M.op X0 X1)
           have i₂ := b1e532 X0 X1 y
           grind)
        | exact superpose b1e532 b1e6365
        | exact resolve b1e6365 b1e532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e6401 : (σ x) = (k (σ x) (M.op y y)) := by
        first
        | (have i₁ := b1e6365 (σ x)
           have i₂ := b1e4207 y
           grind)
        | exact superpose b1e4207 b1e6365
        | exact resolve b1e6365 b1e4207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4207
      have b1e6405 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) y))) := by
        intro X0
        first
        | (have i₁ := b1e99 X0 (M.op (σ X0) y)
           have i₂ := b1e6365 (σ X0)
           grind)
        | exact superpose b1e6365 b1e99
        | exact resolve b1e99 b1e6365
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e6408 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op y (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b1e6405 X0
           have i₂ := b1e36 (σ X0)
           grind)
        | exact superpose b1e36 b1e6405
        | exact resolve b1e6405 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6405
      have b1e6421 : ∀ X0 : G, (k X0 (τ (M.op y (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e6408 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e6408
        | exact resolve b1e6408 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6408
      have b1e7844 : (k x (τ (M.op y y))) = (τ (σ x)) := by
        first
        | (have i₁ := b1e99 x (M.op y y)
           have i₂ := b1e6401
           grind)
        | exact superpose b1e6401 b1e99
        | exact resolve b1e99 b1e6401
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6401
      have b1e7847 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e7844
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e7844
        | exact resolve b1e7844 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7844
      have b1e11444 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op y (σ (σ X0)))))) := by
        intro X0
        first
        | (have i₁ := b1e99 X0 (τ (M.op y (σ (σ X0))))
           have i₂ := b1e6421 (σ X0)
           grind)
        | exact superpose b1e6421 b1e99
        | exact resolve b1e99 b1e6421
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6421
      have b1e11447 : ∀ X0 : G, (k X0 (τ (τ (M.op y (σ (σ X0)))))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e11444 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e11444
        | exact resolve b1e11444 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11444
      have b1e11552 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e89 X0 (σ X0)
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e89
        | exact resolve b1e89 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e11568 : ∀ X0 X1 X2 : G, (σ (M.op y (τ X0))) = (k X0 (σ (M.op X1 X2))) ∨ (M.op X1 X2) = (M.op (τ X0) (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e89 (M.op X1 X2) X0
           have i₂ := b1e532 X1 X2 (τ X0)
           grind)
        | exact superpose b1e532 b1e89
        | (have j0 := b1e89 (M.op X1 X2) X0
           grind)
        | exact resolve b1e89 b1e532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e89 b1e532
      have b1e11614 : ∀ X0 X1 X2 : G, (σ (M.op y (τ X0))) = (k X0 (σ (M.op X1 X2))) ∨ (M.op X1 X2) = (M.op y (τ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e11568 X0 X1 X2
           have i₂ := b1e336 X1 (τ X0) X2
           grind)
        | exact superpose b1e336 b1e11568
        | (have j0 := b1e11568 X0 X1 X2
           grind)
        | exact resolve b1e11568 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11568
      have b1e11630 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e11552 X0 X1
           have i₂ := b1e15 X0 X1
           grind)
        | exact superpose b1e15 b1e11552
        | (have j0 := b1e11552 X0 X1
           grind)
        | exact resolve b1e11552 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11552
      have b1e13216 : ∀ X0 X1 : G, (σ (M.op y (τ X0))) = (k (σ (M.op x X1)) X0) ∨ (τ X0) = (M.op (M.op x X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e94 X0 (M.op x X1)
           have i₂ := b1e29 (τ X0) X1
           grind)
        | exact superpose b1e29 b1e94
        | (have j0 := b1e94 X0 (M.op x X1)
           grind)
        | exact resolve b1e94 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29 b1e94
      have b1e13255 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) y) ∨ (σ (M.op y (τ X0))) = (k (σ (M.op x X1)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e13216 X0 X1
           have i₂ := b1e24 (τ X0) X1
           grind)
        | exact superpose b1e24 b1e13216
        | (have j0 := b1e13216 X0 X1
           grind)
        | exact resolve b1e13216 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24 b1e13216
      have b1e13277 : ∀ X0 X1 : G, (σ (M.op y (τ X0))) = (k (σ (M.op x X1)) X0) ∨ (τ X0) = (M.op y (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13255 X0 X1
           have i₂ := b1e36 (τ X0)
           grind)
        | exact superpose b1e36 b1e13255
        | (have j0 := b1e13255 X0 X1
           grind)
        | exact resolve b1e13255 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13255
      have b1e14289 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e4128 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e4128
        | exact resolve b1e4128 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4128
      have b1e14392 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e14289 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e14289
        | (have j0 := b1e14289 X0 X1
           grind)
        | exact resolve b1e14289 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14289
      have b1e14410 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e14392 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e14392
        | (have j0 := b1e14392 X0 X1
           grind)
        | exact resolve b1e14392 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14392
      have b1e17017 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e4053 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e4053
        | exact resolve b1e4053 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e17027 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k X1 (τ X0))) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e4053 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e4053
        | (have j0 := b1e4053 X1 (τ X0)
           grind)
        | exact resolve b1e4053 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e17050 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ X1) (σ X0)
           have i₂ := b1e4053 X1 X0
           grind)
        | exact superpose b1e4053 b1e13
        | (have j0 := b1e13 (σ X1) (σ X0)
           have j1 := b1e4053 X1 X0
           grind)
        | (have r₁ := b1e13 (σ X0) (σ X1)
           have r₂ := b1e4053 X0 X1
           grind)
        | exact resolve b1e13 b1e4053
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4053
      have b1e17124 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e17050 X0 X1
           have j1 := b1e13 (σ X1) (σ X0)
           grind)
        | (have r₁ := b1e17050 X0 X1
           have r₂ := b1e13 (σ X1) (σ X0)
           grind)
        | exact resolve b1e17050 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17050
      have b1e17138 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k X1 (τ X0))) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e17027 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e17027
        | (have j0 := b1e17027 X0 X1
           grind)
        | exact resolve b1e17027 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17027
      have b1e17144 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e17017 X0 X1
           have i₂ := b1e23 X0 X1
           grind)
        | exact superpose b1e23 b1e17017
        | (have j0 := b1e17017 X0 X1
           grind)
        | exact resolve b1e17017 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17017
      have b1e17159 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e17124 X0 X1
           have i₂ := b1e15 X1 X0
           grind)
        | exact superpose b1e15 b1e17124
        | (have j0 := b1e17124 X0 X1
           grind)
        | exact resolve b1e17124 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17124
      have b1e17160 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b1e17159 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17159
      have b1e17171 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e17138 X0 X1
           have i₂ := b1e23 X0 X1
           grind)
        | exact superpose b1e23 b1e17138
        | (have j0 := b1e17138 X0 X1
           grind)
        | exact resolve b1e17138 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17138
      have b1e17177 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e17144 X0 X1
           have i₂ := b1e22 X0 X1
           grind)
        | exact superpose b1e22 b1e17144
        | (have j0 := b1e17144 X0 X1
           grind)
        | exact resolve b1e17144 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17144
      have b1e17191 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e17171 X0 X1
           have j1 := b1e13 (σ X1) X0
           grind)
        | (have r₁ := b1e17171 X1 X1
           have r₂ := b1e13 (σ X1) X1
           grind)
        | exact resolve b1e17171 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17171
      have b1e17194 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e17177 X0 X1
           have j1 := b1e13 X0 (σ X1)
           grind)
        | (have r₁ := b1e17177 X0 X1
           have r₂ := b1e13 X0 (σ X1)
           grind)
        | exact resolve b1e17177 b1e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17177
      have b1e18134 : ∀ X0 X1 : G, (k X0 (M.op (σ X1) X0)) = X0 ∨ (M.op (σ X1) (σ X1)) = (σ (k X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e4101 X1 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4101
      have b1e18898 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e17160 (τ X0) (τ X1)
           have i₂ := b1e4237 X1 X0
           grind)
        | exact superpose b1e4237 b1e17160
        | (have j0 := b1e17160 (τ X0) (τ X1)
           grind)
        | exact resolve b1e17160 b1e4237
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e18939 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e18898 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e18898
        | (have j0 := b1e18898 X0 X1
           grind)
        | exact resolve b1e18898 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18898
      have b1e18951 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e18939 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e18939
        | (have j0 := b1e18939 X0 X1
           grind)
        | exact resolve b1e18939 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18939
      have b1e18955 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e18951 X0 X1
           have i₂ := b1e23 X0 (τ X1)
           grind)
        | exact superpose b1e23 b1e18951
        | (have j0 := b1e18951 X0 X1
           grind)
        | exact resolve b1e18951 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18951
      have b1e18957 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e18955 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e18955
        | (have j0 := b1e18955 X0 X1
           grind)
        | exact resolve b1e18955 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18955
      have b1e18959 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 y) = (k (M.op X0 y) X0) := by
        intro X0
        first
        | (have i₁ := b1e18957 X0 (M.op X0 y)
           have i₂ := b1e6365 X0
           grind)
        | exact superpose b1e6365 b1e18957
        | (have j0 := b1e18957 X0 (M.op X0 y)
           grind)
        | (have r₁ := b1e18957 X0 (M.op X0 y)
           have r₂ := b1e6365 X0
           grind)
        | exact resolve b1e18957 b1e6365
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e18965 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op y y) = (k (M.op y y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e18957 (M.op X0 X1) (M.op y y)
           have i₂ := b1e6394 X0 X1
           grind)
        | exact superpose b1e6394 b1e18957
        | (have j0 := b1e18957 (M.op X0 X1) (M.op y y)
           grind)
        | (have r₁ := b1e18957 (M.op X0 X1) (M.op y y)
           have r₂ := b1e6394 X0 X1
           grind)
        | exact resolve b1e18957 b1e6394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e18975 : x ≠ x ∨ (τ (M.op y y)) = (k (τ (M.op y y)) x) := by
        first
        | (have i₁ := b1e18957 x (τ (M.op y y))
           have i₂ := b1e7847
           grind)
        | exact superpose b1e7847 b1e18957
        | (have j0 := b1e18957 x (τ (M.op y y))
           grind)
        | (have r₁ := b1e18957 x (τ (M.op y y))
           have r₂ := b1e7847
           grind)
        | exact resolve b1e18957 b1e7847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7847
      have b1e18978 : (τ (M.op y y)) = (k (τ (M.op y y)) x) := by grind
      clear b1e18975
      have b1e18981 : ∀ X0 X1 : G, (M.op y y) = (k (M.op y y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e18965 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18965
      have b1e18987 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) X0) := by
        intro X0
        first
        | (have j0 := b1e18959 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18959
      have b1e19698 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e14410 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e14410
        | exact resolve b1e14410 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14410
      have b1e19952 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e17194 X0 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e17194
        | exact resolve b1e17194 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17194
      have b1e20234 : (τ (σ x)) = (k y (τ y)) ∨ y = (M.op (σ y) y) := by
        first
        | (have i₁ := b1e4264 y y
           have i₂ := b1e5901
           grind)
        | exact superpose b1e5901 b1e4264
        | (have j0 := b1e4264 y y
           grind)
        | exact resolve b1e4264 b1e5901
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4264
      have b1e20255 : x = (k y (τ y)) ∨ y = (M.op (σ y) y) := by
        first
        | (have i₁ := b1e20234
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e20234
        | exact resolve b1e20234 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20234
      have b1e20302 : y = (M.op y (σ y)) ∨ x = (k y (τ y)) := by
        first
        | (have i₁ := b1e20255
           have i₂ := b1e36 (σ y)
           grind)
        | exact superpose b1e36 b1e20255
        | exact resolve b1e20255 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20255
      have b1e20334 : x = (k y (τ y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e20302
           have i₂ := b1e5901
           grind)
        | exact superpose b1e5901 b1e20302
        | exact resolve b1e20302 b1e5901
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20302
      have b1e20386 : (σ x) = (k (σ y) y) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e23 y y
           have i₂ := b1e20334
           grind)
        | exact superpose b1e20334 b1e23
        | exact resolve b1e23 b1e20334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20671 : (σ x) = (σ y) ∨ (M.op (σ y) y) = (k y (σ y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e17191 y y
           have i₂ := b1e20386
           grind)
        | exact superpose b1e20386 b1e17191
        | (have j0 := b1e17191 y y
           grind)
        | exact resolve b1e17191 b1e20386
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17191 b1e20386
      have b1e20681 : (M.op (σ y) y) = (k y (σ y)) ∨ y = (σ x) := by
        first
        | (have r₁ := b1e20671
           have r₂ := b1e6018
           grind)
        | exact resolve b1e20671 b1e6018
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20671
      have b1e20688 : (M.op y (σ y)) = (k y (σ y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e20681
           have i₂ := b1e36 (σ y)
           grind)
        | exact superpose b1e36 b1e20681
        | exact resolve b1e20681 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20681
      have b1e20690 : (σ x) = (k y (σ y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e20688
           have i₂ := b1e5901
           grind)
        | exact superpose b1e5901 b1e20688
        | exact resolve b1e20688 b1e5901
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20688
      have b1e21328 : x = (M.op (τ y) y) ∨ x = y ∨ y = (σ x) := by
        first
        | (have i₁ := b1e19698 (τ y) y
           have i₂ := b1e20334
           grind)
        | exact superpose b1e20334 b1e19698
        | exact resolve b1e19698 b1e20334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20334
      have b1e21401 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e19698 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19698
      have b1e21422 : x = (M.op y (τ y)) ∨ x = y ∨ y = (σ x) := by
        first
        | (have i₁ := b1e21328
           have i₂ := b1e36 (τ y)
           grind)
        | exact superpose b1e36 b1e21328
        | exact resolve b1e21328 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21328
      have b1e21849 : ∀ X0 : G, y ≠ (M.op y X0) ∨ y = (k y X0) := by
        intro X0
        first
        | (have i₁ := b1e21401 y X0
           have i₂ := b1e36 X0
           grind)
        | (have i₁ := b1e21401 X0 y
           have i₂ := b1e36 X0
           grind)
        | exact superpose b1e36 b1e21401
        | (have j0 := b1e21401 y X0
           grind)
        | exact resolve b1e21401 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e21869 : ∀ X0 X1 X2 : G, (M.op X0 y) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e21401 X0 (M.op X1 X2)
           have i₂ := b1e191 X1 X2 X0
           grind)
        | exact superpose b1e191 b1e21401
        | (have j0 := b1e21401 X0 (M.op X1 X2)
           grind)
        | exact resolve b1e21401 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e22182 : y ≠ (σ x) ∨ y = (k y (σ y)) := by
        first
        | (have i₁ := b1e21849 (σ y)
           have i₂ := b1e5901
           grind)
        | exact superpose b1e5901 b1e21849
        | (have j0 := b1e21849 (σ y)
           grind)
        | exact resolve b1e21849 b1e5901
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21849
      have b1e26576 : ∀ X0 X1 : G, x ≠ y ∨ x = (k x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e21869 x X0 X1
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e21869
        | (have j0 := b1e21869 x X0 X1
           grind)
        | exact resolve b1e21869 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30587 : x = (k x (M.op y y)) ∨ x = y ∨ y = (σ x) := by
        first
        | (have i₁ := b1e6394 y (τ y)
           have i₂ := b1e21422
           grind)
        | exact superpose b1e21422 b1e6394
        | exact resolve b1e6394 b1e21422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21422
      have b1e30595 : x = (k x (M.op y y)) ∨ y = (σ x) := by
        first
        | (have j1 := b1e26576 y y
           grind)
        | (have r₁ := b1e30587
           have r₂ := b1e26576 x x
           grind)
        | exact resolve b1e30587 b1e26576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30587
      have b1e30700 : (σ x) = (σ (M.op (M.op y y) x)) ∨ (M.op y y) = (M.op x (M.op y y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e11630 x (M.op y y)
           have i₂ := b1e30595
           grind)
        | exact superpose b1e30595 b1e11630
        | (have j0 := b1e11630 x (M.op y y)
           grind)
        | exact resolve b1e11630 b1e30595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30595
      have b1e30706 : (σ (M.op x y)) = (σ x) ∨ (M.op y y) = (M.op x (M.op y y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e30700
           have i₂ := b1e86 x y
           grind)
        | exact superpose b1e86 b1e30700
        | exact resolve b1e30700 b1e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30700
      have b1e30711 : (σ x) = (σ y) ∨ (M.op y y) = (M.op x (M.op y y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e30706
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e30706
        | exact resolve b1e30706 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30706
      have b1e30714 : (M.op y y) = (M.op x (M.op y y)) ∨ y = (σ x) := by
        first
        | (have r₁ := b1e30711
           have r₂ := b1e6018
           grind)
        | exact resolve b1e30711 b1e6018
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30711
      have b1e30717 : (M.op y x) = (M.op y y) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e30714
           have i₂ := b1e336 y x y
           grind)
        | exact superpose b1e336 b1e30714
        | exact resolve b1e30714 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30714
      have b1e30718 : y = (M.op y y) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e30717
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e30717
        | exact resolve b1e30717 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30717
      have b1e30870 : ∀ X0 X1 : G, y ≠ y ∨ y = (k y (M.op X0 X1)) ∨ y = (σ x) := by
        intro X0 X1
        first
        | (have i₁ := b1e21869 y X0 X1
           have i₂ := b1e30718
           grind)
        | exact superpose b1e30718 b1e21869
        | (have j0 := b1e21869 y X0 X1
           grind)
        | (have r₁ := b1e21869 y X1 x
           have r₂ := b1e30718
           grind)
        | exact resolve b1e21869 b1e30718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21869
      have b1e30916 : y ≠ y ∨ y = (k y y) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e21401 y y
           have i₂ := b1e30718
           grind)
        | exact superpose b1e30718 b1e21401
        | (have j0 := b1e21401 y y
           grind)
        | (have r₁ := b1e21401 y y
           have r₂ := b1e30718
           grind)
        | exact resolve b1e21401 b1e30718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30718
      have b1e30917 : y = (k y y) ∨ y = (σ x) := by grind
      clear b1e30916
      have b1e30923 : ∀ X0 X1 : G, y = (k y (M.op X0 X1)) ∨ y = (σ x) := by
        intro X0 X1
        first
        | (have j0 := b1e30870 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30870
      have b1e31337 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e4108 y
           have i₂ := b1e30917
           grind)
        | exact superpose b1e30917 b1e4108
        | (have j0 := b1e4108 y
           grind)
        | exact resolve b1e4108 b1e30917
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30917
      have b1e31346 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (σ x) := by grind
      clear b1e31337
      have b1e34381 : y = (k y (σ y)) ∨ y = (σ x) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e30923 (σ y) (σ y)
           have i₂ := b1e31346
           grind)
        | exact superpose b1e31346 b1e30923
        | exact resolve b1e30923 b1e31346
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30923 b1e31346
      have b1e34382 : y = (k y (σ y)) ∨ y = (σ x) := by grind
      clear b1e34381
      have b1e34392 : y = (k y (σ y)) := by
        first
        | (have r₁ := b1e34382
           have r₂ := b1e22182
           grind)
        | exact resolve b1e34382 b1e22182
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22182 b1e34382
      have b1e34697 : y = (σ x) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e20690
           have i₂ := b1e34392
           grind)
        | exact superpose b1e34392 b1e20690
        | exact resolve b1e20690 b1e34392
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20690 b1e34392
      have b1e34720 : y = (σ x) := by grind
      clear b1e34697
      have b1e34978 : y ≠ (σ y) := by
        first
        | (have i₁ := b1e6018
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e6018
        | exact resolve b1e6018 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6018
      have b1e34986 : x = (τ y) := by
        first
        | (have i₁ := b1e11 x
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e11
        | exact resolve b1e11 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34987 : ∀ X0 : G, (σ (k x X0)) = (k y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 x X0
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e15
        | exact resolve b1e15 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34988 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) y) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 x
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e15
        | exact resolve b1e15 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34997 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b1e92 X0 x
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e92
        | exact resolve b1e92 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e92
      have b1e35002 : ∀ X0 : G, (k x (τ X0)) = (τ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b1e99 x X0
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e99
        | exact resolve b1e99 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e99
      have b1e35028 : x = (k x (τ (τ (M.op y (σ y))))) := by
        first
        | (have i₁ := b1e11447 x
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e11447
        | exact resolve b1e11447 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11447
      have b1e35052 : x = (k x (τ (τ (σ x)))) := by
        first
        | (have i₁ := b1e35028
           have i₂ := b1e5901
           grind)
        | exact superpose b1e5901 b1e35028
        | exact resolve b1e35028 b1e5901
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5901 b1e35028
      have b1e35064 : x = (k x (τ x)) := by
        first
        | (have i₁ := b1e35052
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e35052
        | exact resolve b1e35052 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35052
      have b1e36055 : x = (M.op (τ x) x) ∨ (τ x) = (M.op x (τ x)) := by
        first
        | (have i₁ := b1e14 x (τ x)
           have i₂ := b1e35064
           grind)
        | exact superpose b1e35064 b1e14
        | (have j0 := b1e14 (τ x) x
           grind)
        | exact resolve b1e14 b1e35064
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e37230 : (k y y) = (σ (k x x)) := by
        first
        | (have i₁ := b1e34987 x
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e34987
        | exact resolve b1e34987 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34987
      have b1e37933 : (σ (k (k x x) x)) = (k (k y y) y) := by
        first
        | (have i₁ := b1e34988 (k x x)
           have i₂ := b1e37230
           grind)
        | exact superpose b1e37230 b1e34988
        | exact resolve b1e34988 b1e37230
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37230
      have b1e37963 : ∀ X0 : G, (σ (M.op y (τ y))) = (σ (k (M.op x X0) x)) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e13277 y X0
           have i₂ := b1e34988 (M.op x X0)
           grind)
        | exact superpose b1e34988 b1e13277
        | (have j0 := b1e13277 y x
           grind)
        | exact resolve b1e13277 b1e34988
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34988
      have b1e37995 : ∀ X0 : G, (σ (M.op y x)) = (σ (k (M.op x X0) x)) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e37963 X0
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e37963
        | exact resolve b1e37963 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37963
      have b1e38033 : ∀ X0 : G, (σ y) = (σ (k (M.op x X0) x)) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e37995 X0
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e37995
        | exact resolve b1e37995 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37995
      have b1e38039 : ∀ X0 : G, x = (M.op y x) ∨ (σ y) = (σ (k (M.op x X0) x)) := by
        intro X0
        first
        | (have i₁ := b1e38033 X0
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e38033
        | (have j0 := b1e38033 X0
           grind)
        | exact resolve b1e38033 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38033
      have b1e38041 : ∀ X0 : G, (σ y) = (σ (k (M.op x X0) x)) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b1e38039 X0
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e38039
        | (have j0 := b1e38039 X0
           grind)
        | exact resolve b1e38039 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38039
      have b1e38287 : ∀ X0 : G, (k (τ (σ (M.op x X0))) x) = (τ (σ (M.op y (τ y)))) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e34997 (σ (M.op x X0))
           have i₂ := b1e13277 y X0
           grind)
        | exact superpose b1e13277 b1e34997
        | (have j1 := b1e13277 y x
           grind)
        | exact resolve b1e34997 b1e13277
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13277 b1e34997
      have b1e38369 : ∀ X0 : G, (M.op y (τ y)) = (k (τ (σ (M.op x X0))) x) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e38287 X0
           have i₂ := b1e11 (M.op y (τ y))
           grind)
        | exact superpose b1e11 b1e38287
        | exact resolve b1e38287 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38287
      have b1e38376 : ∀ X0 : G, (k (M.op x X0) x) = (M.op y (τ y)) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e38369 X0
           have i₂ := b1e11 (M.op x X0)
           grind)
        | exact superpose b1e11 b1e38369
        | exact resolve b1e38369 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38369
      have b1e38380 : ∀ X0 : G, (M.op y x) = (k (M.op x X0) x) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e38376 X0
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e38376
        | exact resolve b1e38376 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38376
      have b1e38382 : ∀ X0 : G, y = (k (M.op x X0) x) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b1e38380 X0
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e38380
        | exact resolve b1e38380 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38380
      have b1e38383 : ∀ X0 : G, x = (M.op y x) ∨ y = (k (M.op x X0) x) := by
        intro X0
        first
        | (have i₁ := b1e38382 X0
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e38382
        | (have j0 := b1e38382 X0
           grind)
        | exact resolve b1e38382 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38382
      have b1e38384 : ∀ X0 : G, y = (k (M.op x X0) x) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b1e38383 X0
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e38383
        | (have j0 := b1e38383 X0
           grind)
        | exact resolve b1e38383 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38383
      have b1e38746 : ∀ X0 X1 : G, (τ (σ (M.op y (τ y)))) = (k x (τ (σ (M.op X0 X1)))) ∨ (M.op X0 X1) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e35002 (σ (M.op X0 X1))
           have i₂ := b1e11614 y X0 X1
           grind)
        | exact superpose b1e11614 b1e35002
        | (have j1 := b1e11614 y X0 X1
           grind)
        | exact resolve b1e35002 b1e11614
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11614
      have b1e38829 : ∀ X0 X1 : G, (k x (M.op X0 X1)) = (τ (σ (M.op y (τ y)))) ∨ (M.op X0 X1) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e38746 X0 X1
           have i₂ := b1e11 (M.op X0 X1)
           grind)
        | exact superpose b1e11 b1e38746
        | (have j0 := b1e38746 X0 X1
           grind)
        | exact resolve b1e38746 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38746
      have b1e38842 : ∀ X0 X1 : G, (k x (M.op X0 X1)) = (M.op y (τ y)) ∨ (M.op X0 X1) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e38829 X0 X1
           have i₂ := b1e11 (M.op y (τ y))
           grind)
        | exact superpose b1e11 b1e38829
        | (have j0 := b1e38829 X0 X1
           grind)
        | exact resolve b1e38829 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38829
      have b1e38848 : ∀ X0 X1 : G, (M.op y x) = (k x (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e38842 X0 X1
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e38842
        | (have j0 := b1e38842 X0 X1
           grind)
        | exact resolve b1e38842 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38842
      have b1e38849 : ∀ X0 X1 : G, y = (k x (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e38848 X0 X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e38848
        | (have j0 := b1e38848 X0 X1
           grind)
        | exact resolve b1e38848 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38848
      have b1e38850 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y x) ∨ y = (k x (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e38849 X0 X1
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e38849
        | (have j0 := b1e38849 X0 X1
           grind)
        | exact resolve b1e38849 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38849
      have b1e38851 : ∀ X0 X1 : G, y = (k x (M.op X0 X1)) ∨ (M.op X0 X1) = y := by
        intro X0 X1
        first
        | (have i₁ := b1e38850 X0 X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e38850
        | (have j0 := b1e38850 X0 X1
           grind)
        | exact resolve b1e38850 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38850
      have b1e53576 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 X3)) = (M.op (M.op X0 X1) (M.op (τ x) X2)) ∨ (τ x) = (M.op x (τ x)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e178 X0 X1 (τ x) X2 X3 x
           have i₂ := b1e36055
           grind)
        | exact superpose b1e36055 b1e178
        | exact resolve b1e178 b1e36055
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e178 b1e36055
      have b1e53606 : ∀ X0 X1 X3 : G, (M.op y (M.op X0 X1)) = (M.op x (M.op X0 X3)) ∨ (τ x) = (M.op x (τ x)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b1e53576 X0 X1 x X3
           have i₂ := b1e336 (τ x) (M.op X0 X1) x
           grind)
        | exact superpose b1e336 b1e53576
        | exact resolve b1e53576 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53576
      have b1e53635 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y x) ∨ (τ x) = (M.op x (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e53606 X0 X1 x
           have i₂ := b1e336 X0 x x
           grind)
        | exact superpose b1e336 b1e53606
        | exact resolve b1e53606 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53606
      have b1e53647 : ∀ X0 X1 : G, y = (M.op y (M.op X0 X1)) ∨ (τ x) = (M.op x (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e53635 X0 X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e53635
        | exact resolve b1e53635 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53635
      have b1e53655 : (τ x) = (M.op x (τ x)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e53647 x x
           have i₂ := b1e336 x y x
           grind)
        | exact superpose b1e336 b1e53647
        | exact resolve b1e53647 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53647
      have b1e54183 : y = (k x (τ x)) ∨ y = (τ x) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e38851 x (τ x)
           have i₂ := b1e53655
           grind)
        | exact superpose b1e53655 b1e38851
        | (have j0 := b1e38851 y y
           grind)
        | exact resolve b1e38851 b1e53655
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53655
      have b1e54186 : y = (M.op y y) ∨ y = (τ x) ∨ x = y := by
        first
        | (have i₁ := b1e54183
           have i₂ := b1e35064
           grind)
        | exact superpose b1e35064 b1e54183
        | exact resolve b1e54183 b1e35064
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35064 b1e54183
      have b1e54778 : (τ y) = (k (τ y) x) ∨ y = (τ x) ∨ x = y := by
        first
        | (have i₁ := b1e18978
           have i₂ := b1e54186
           grind)
        | exact superpose b1e54186 b1e18978
        | exact resolve b1e18978 b1e54186
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54186
      have b1e54928 : x = (k x x) ∨ y = (τ x) ∨ x = y := by
        first
        | (have i₁ := b1e54778
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e54778
        | exact resolve b1e54778 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54778
      have b1e56579 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (τ x) ∨ x = y := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e54928
           grind)
        | exact superpose b1e54928 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e54928
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54928
      have b1e56589 : x = (M.op x x) ∨ y = (τ x) ∨ x = y := by grind
      clear b1e56579
      have b1e59194 : x = (k x (M.op y y)) ∨ y = (τ x) ∨ x = y := by
        first
        | (have i₁ := b1e6394 x x
           have i₂ := b1e56589
           grind)
        | exact superpose b1e56589 b1e6394
        | exact resolve b1e6394 b1e56589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6394
      have b1e59215 : x = (k x (M.op y y)) ∨ y = (τ x) := by
        first
        | (have j1 := b1e26576 y y
           grind)
        | (have r₁ := b1e59194
           have r₂ := b1e26576 x x
           grind)
        | exact resolve b1e59194 b1e26576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26576 b1e59194
      have b1e59427 : (σ x) = (σ (M.op (M.op y y) x)) ∨ (M.op y y) = (M.op x (M.op y y)) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e11630 x (M.op y y)
           have i₂ := b1e59215
           grind)
        | exact superpose b1e59215 b1e11630
        | (have j0 := b1e11630 x (M.op y y)
           grind)
        | exact resolve b1e11630 b1e59215
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11630 b1e59215
      have b1e59443 : (σ (M.op x y)) = (σ x) ∨ (M.op y y) = (M.op x (M.op y y)) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e59427
           have i₂ := b1e86 x y
           grind)
        | exact superpose b1e86 b1e59427
        | exact resolve b1e59427 b1e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e86 b1e59427
      have b1e59449 : y = (σ (M.op x y)) ∨ (M.op y y) = (M.op x (M.op y y)) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e59443
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e59443
        | exact resolve b1e59443 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59443
      have b1e59453 : y = (σ y) ∨ (M.op y y) = (M.op x (M.op y y)) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e59449
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e59449
        | exact resolve b1e59449 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59449
      have b1e59456 : (M.op y y) = (M.op x (M.op y y)) ∨ y = (τ x) := by
        first
        | (have r₁ := b1e59453
           have r₂ := b1e34978
           grind)
        | exact resolve b1e59453 b1e34978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59453
      have b1e59457 : (M.op y x) = (M.op y y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e59456
           have i₂ := b1e336 y x y
           grind)
        | exact superpose b1e336 b1e59456
        | exact resolve b1e59456 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e336 b1e59456
      have b1e59458 : y = (M.op y y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e59457
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e59457
        | exact resolve b1e59457 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e61 b1e59457
      have b1e59751 : (τ y) = (k (τ y) x) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e18978
           have i₂ := b1e59458
           grind)
        | exact superpose b1e59458 b1e18978
        | exact resolve b1e18978 b1e59458
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18978
      have b1e59848 : y ≠ y ∨ y = (k y y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e21401 y y
           have i₂ := b1e59458
           grind)
        | exact superpose b1e59458 b1e21401
        | (have j0 := b1e21401 y y
           grind)
        | (have r₁ := b1e21401 y y
           have r₂ := b1e59458
           grind)
        | exact resolve b1e21401 b1e59458
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21401 b1e59458
      have b1e59852 : y = (k y y) ∨ y = (τ x) := by grind
      clear b1e59848
      have b1e59903 : x = (k x x) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e59751
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e59751
        | exact resolve b1e59751 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59751
      have b1e60385 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e4108 y
           have i₂ := b1e59852
           grind)
        | exact superpose b1e59852 b1e4108
        | (have j0 := b1e4108 y
           grind)
        | exact resolve b1e4108 b1e59852
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4108 b1e59852
      have b1e60397 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (τ x) := by grind
      clear b1e60385
      have b1e60853 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e59903
           grind)
        | exact superpose b1e59903 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e59903
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59903
      have b1e60863 : x = (M.op x x) ∨ y = (τ x) := by grind
      clear b1e60853
      have b1e61372 : ∀ X0 : G, (M.op X0 y) = (M.op x X0) ∨ y = (τ x) := by
        intro X0
        first
        | (have i₁ := b1e191 x x X0
           have i₂ := b1e60863
           grind)
        | exact superpose b1e60863 b1e191
        | exact resolve b1e191 b1e60863
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e191 b1e60863
      have b1e63383 : x = (M.op x y) ∨ y = (τ x) ∨ x = y ∨ y = (τ x) := by
        first
        | (have i₁ := b1e56589
           have i₂ := b1e61372 x
           grind)
        | exact superpose b1e61372 b1e56589
        | exact resolve b1e56589 b1e61372
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e56589 b1e61372
      have b1e63477 : x = (M.op x y) ∨ y = (τ x) ∨ x = y := by grind
      clear b1e63383
      have b1e63520 : x = y ∨ y = (τ x) ∨ x = y := by
        first
        | (have i₁ := b1e63477
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e63477
        | exact resolve b1e63477 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e63477
      have b1e63521 : y = (τ x) ∨ x = y := by grind
      clear b1e63520
      have b1e87792 : y = (k x (σ y)) ∨ y = (σ y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e38851 (σ y) (σ y)
           have i₂ := b1e60397
           grind)
        | exact superpose b1e60397 b1e38851
        | exact resolve b1e38851 b1e60397
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38851 b1e60397
      have b1e87807 : y = (k x (σ y)) ∨ y = (τ x) := by
        first
        | (have r₁ := b1e87792
           have r₂ := b1e34978
           grind)
        | exact resolve b1e87792 b1e34978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e87792
      have b1e88575 : x ≠ y ∨ (σ y) = (k (σ y) x) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e18957 x (σ y)
           have i₂ := b1e87807
           grind)
        | exact superpose b1e87807 b1e18957
        | (have j0 := b1e18957 x (σ y)
           grind)
        | exact resolve b1e18957 b1e87807
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e88577 : (σ y) = (k (σ y) x) ∨ y = (τ x) := by
        first
        | (have r₁ := b1e88575
           have r₂ := b1e63521
           grind)
        | exact resolve b1e88575 b1e63521
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e63521 b1e88575
      have b1e90086 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ x) = (σ (k x (σ y))) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e17160 (σ y) x
           have i₂ := b1e88577
           grind)
        | exact superpose b1e88577 b1e17160
        | (have j0 := b1e17160 (σ y) x
           grind)
        | exact resolve b1e17160 b1e88577
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e88577
      have b1e90094 : (σ x) = (σ (k x (σ y))) ∨ y = (τ x) := by grind
      clear b1e90086
      have b1e90105 : y = (σ (k x (σ y))) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e90094
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e90094
        | exact resolve b1e90094 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e90094
      have b1e92307 : y = (σ y) ∨ y = (τ x) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e90105
           have i₂ := b1e87807
           grind)
        | exact superpose b1e87807 b1e90105
        | exact resolve b1e90105 b1e87807
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e87807 b1e90105
      have b1e92479 : y = (σ y) ∨ y = (τ x) := by grind
      clear b1e92307
      have b1e92528 : y = (τ x) := by
        first
        | (have r₁ := b1e92479
           have r₂ := b1e34978
           grind)
        | exact resolve b1e92479 b1e34978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e92479
      have b1e92915 : x = (σ y) := by
        first
        | (have i₁ := b1e12 x
           have i₂ := b1e92528
           grind)
        | exact superpose b1e92528 b1e12
        | exact resolve b1e12 b1e92528
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e92916 : ∀ X0 : G, (σ (k y X0)) = (k x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e22 x X0
           have i₂ := b1e92528
           grind)
        | exact superpose b1e92528 b1e22
        | exact resolve b1e22 b1e92528
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e92917 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) x) := by
        intro X0
        first
        | (have i₁ := b1e23 x X0
           have i₂ := b1e92528
           grind)
        | exact superpose b1e92528 b1e23
        | exact resolve b1e23 b1e92528
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23
      have b1e92924 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b1e4237 x X0
           have i₂ := b1e92528
           grind)
        | exact superpose b1e92528 b1e4237
        | exact resolve b1e4237 b1e92528
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4237 b1e92528
      have b1e93273 : x ≠ y := by
        first
        | (have i₁ := b1e34978
           have i₂ := b1e92915
           grind)
        | exact superpose b1e92915 b1e34978
        | exact resolve b1e34978 b1e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34978
      have b1e94630 : (σ (k y y)) = (k x x) := by
        first
        | (have i₁ := b1e92916 y
           have i₂ := b1e92915
           grind)
        | exact superpose b1e92915 b1e92916
        | exact resolve b1e92916 b1e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e95269 : (k x (k x x)) = (σ (k y (k y y))) := by
        first
        | (have i₁ := b1e92916 (k y y)
           have i₂ := b1e94630
           grind)
        | exact superpose b1e94630 b1e92916
        | exact resolve b1e92916 b1e94630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e92916
      have b1e95683 : ∀ X0 : G, (σ (k (k (M.op x X0) x) y)) = (k (σ y) x) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b1e92917 (k (M.op x X0) x)
           have i₂ := b1e38041 X0
           grind)
        | exact superpose b1e38041 b1e92917
        | exact resolve b1e92917 b1e38041
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38041
      have b1e95863 : ∀ X0 : G, (σ (k (k (M.op x X0) x) y)) = (k (σ y) x) := by
        intro X0
        first
        | (have j0 := b1e95683 X0
           grind)
        | (have r₁ := b1e95683 X0
           have r₂ := b1e93273
           grind)
        | exact resolve b1e95683 b1e93273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e95683
      have b1e95900 : ∀ X0 : G, (σ (k y y)) = (σ (k (k (M.op x X0) x) y)) := by
        intro X0
        first
        | (have i₁ := b1e95863 X0
           have i₂ := b1e92917 y
           grind)
        | exact superpose b1e92917 b1e95863
        | exact resolve b1e95863 b1e92917
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e92917 b1e95863
      have b1e95916 : ∀ X0 : G, (k x x) = (σ (k (k (M.op x X0) x) y)) := by
        intro X0
        first
        | (have i₁ := b1e95900 X0
           have i₂ := b1e94630
           grind)
        | exact superpose b1e94630 b1e95900
        | exact resolve b1e95900 b1e94630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e95900
      have b1e96230 : ∀ X0 : G, (τ y) = (k (τ (M.op x X0)) y) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b1e92924 (M.op x X0)
           have i₂ := b1e38384 X0
           grind)
        | exact superpose b1e38384 b1e92924
        | exact resolve b1e92924 b1e38384
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38384 b1e92924
      have b1e96384 : ∀ X0 : G, (τ y) = (k (τ (M.op x X0)) y) := by
        intro X0
        first
        | (have j0 := b1e96230 X0
           grind)
        | (have r₁ := b1e96230 X0
           have r₂ := b1e93273
           grind)
        | exact resolve b1e96230 b1e93273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96230
      have b1e96393 : ∀ X0 : G, x = (k (τ (M.op x X0)) y) := by
        intro X0
        first
        | (have i₁ := b1e96384 X0
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e96384
        | exact resolve b1e96384 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96384
      have b1e96691 : ∀ X0 : G, (σ x) = (k (M.op x X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e22 (M.op x X0) y
           have i₂ := b1e96393 X0
           grind)
        | exact superpose b1e96393 b1e22
        | exact resolve b1e22 b1e96393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22 b1e96393
      have b1e96791 : ∀ X0 : G, (σ x) = (k (M.op x X0) x) := by
        intro X0
        first
        | (have i₁ := b1e96691 X0
           have i₂ := b1e92915
           grind)
        | exact superpose b1e92915 b1e96691
        | exact resolve b1e96691 b1e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96691
      have b1e96831 : ∀ X0 : G, y = (k (M.op x X0) x) := by
        intro X0
        first
        | (have i₁ := b1e96791 X0
           have i₂ := b1e34720
           grind)
        | exact superpose b1e34720 b1e96791
        | exact resolve b1e96791 b1e34720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34720 b1e96791
      have b1e112582 : ∀ X0 : G, (k x x) = (σ (k (M.op x X0) x)) ∨ (k y (k (M.op x X0) x)) = (M.op (k (M.op x X0) x) y) := by
        intro X0
        first
        | (have i₁ := b1e95916 X0
           have i₂ := b1e19952 y (k (M.op x X0) x)
           grind)
        | exact superpose b1e19952 b1e95916
        | (have j1 := b1e19952 y (k (M.op x X0) x)
           grind)
        | exact resolve b1e95916 b1e19952
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e95916
      have b1e112764 : ∀ X0 : G, (σ y) = (k x x) ∨ (k y (k (M.op x X0) x)) = (M.op (k (M.op x X0) x) y) := by
        intro X0
        first
        | (have i₁ := b1e112582 X0
           have i₂ := b1e96831 X0
           grind)
        | exact superpose b1e96831 b1e112582
        | (have j0 := b1e112582 X0
           grind)
        | exact resolve b1e112582 b1e96831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e112582
      have b1e112825 : ∀ X0 : G, x = (k x x) ∨ (k y (k (M.op x X0) x)) = (M.op (k (M.op x X0) x) y) := by
        intro X0
        first
        | (have i₁ := b1e112764 X0
           have i₂ := b1e92915
           grind)
        | exact superpose b1e92915 b1e112764
        | (have j0 := b1e112764 X0
           grind)
        | exact resolve b1e112764 b1e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e112764
      have b1e112859 : ∀ X0 : G, (k y (k (M.op x X0) x)) = (M.op y (k (M.op x X0) x)) ∨ x = (k x x) := by
        intro X0
        first
        | (have i₁ := b1e112825 X0
           have i₂ := b1e36 (k (M.op x X0) x)
           grind)
        | exact superpose b1e36 b1e112825
        | exact resolve b1e112825 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36 b1e112825
      have b1e112871 : x = (k x x) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b1e112859 x
           have i₂ := b1e96831 x
           grind)
        | exact superpose b1e96831 b1e112859
        | exact resolve b1e112859 b1e96831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e112859
      have b1e115353 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e112871
           grind)
        | exact superpose b1e112871 b1e14
        | (have j0 := b1e14 y y
           grind)
        | exact resolve b1e14 b1e112871
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e115359 : (M.op y y) = (k y y) ∨ x = (M.op x x) := by grind
      clear b1e115353
      have b1e116651 : (σ (k y (M.op y y))) = (k x (k x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e95269
           have i₂ := b1e115359
           grind)
        | exact superpose b1e115359 b1e95269
        | exact resolve b1e95269 b1e115359
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e95269 b1e115359
      have b1e116699 : (σ y) = (k x (k x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e116651
           have i₂ := b1e6365 y
           grind)
        | exact superpose b1e6365 b1e116651
        | exact resolve b1e116651 b1e6365
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6365 b1e116651
      have b1e116711 : x = (k x (k x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e116699
           have i₂ := b1e92915
           grind)
        | exact superpose b1e92915 b1e116699
        | exact resolve b1e116699 b1e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e116699
      have b1e117783 : x = (k x (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e116711
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e116711
        | (have j1 := b1e14 x x
           grind)
        | exact resolve b1e116711 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e116711
      have b1e117801 : x = (k x (M.op x x)) ∨ x = (M.op x x) := by grind
      clear b1e117783
      have b1e118295 : (σ x) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (k (M.op x x) x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e17160 x (M.op x x)
           have i₂ := b1e117801
           grind)
        | exact superpose b1e117801 b1e17160
        | (have j0 := b1e17160 x (M.op x x)
           grind)
        | exact resolve b1e17160 b1e117801
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17160
      have b1e118296 : x ≠ x ∨ (M.op x x) = (k (M.op x x) x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e18957 x (M.op x x)
           have i₂ := b1e117801
           grind)
        | exact superpose b1e117801 b1e18957
        | (have j0 := b1e18957 x (M.op x x)
           grind)
        | (have r₁ := b1e18957 x (M.op x x)
           have r₂ := b1e117801
           grind)
        | exact resolve b1e18957 b1e117801
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18957 b1e117801
      have b1e118297 : (M.op x x) = (k (M.op x x) x) ∨ x = (M.op x x) := by grind
      clear b1e118296
      have b1e118298 : (σ (M.op x x)) = (σ (k (M.op x x) x)) ∨ x = (M.op x x) := by grind
      clear b1e118295
      have b1e118300 : x = (M.op x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e118297
           have i₂ := b1e96831 x
           grind)
        | exact superpose b1e96831 b1e118297
        | exact resolve b1e118297 b1e96831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e118297
      have b1e118301 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e118298
           have i₂ := b1e96831 x
           grind)
        | exact superpose b1e96831 b1e118298
        | exact resolve b1e118298 b1e96831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e118298
      have b1e118318 : x = (σ (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e118301
           have i₂ := b1e92915
           grind)
        | exact superpose b1e92915 b1e118301
        | exact resolve b1e118301 b1e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e118301
      have b1e118489 : y = (k x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e96831 x
           have i₂ := b1e118300
           grind)
        | exact superpose b1e118300 b1e96831
        | exact resolve b1e96831 b1e118300
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e96831 b1e118300
      have b1e119518 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b1e19952 x x
           have i₂ := b1e118489
           grind)
        | exact superpose b1e118489 b1e19952
        | exact resolve b1e19952 b1e118489
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19952 b1e118489
      have b1e119519 : x = y ∨ y = (M.op x x) := by grind
      clear b1e119518
      have b1e119530 : y = (M.op x x) := by
        first
        | (have r₁ := b1e119519
           have r₂ := b1e93273
           grind)
        | exact resolve b1e119519 b1e93273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e119519
      have b1e123370 : ∀ X0 : G, (M.op x x) = (σ (k (M.op x x) (M.op x x))) ∨ (k X0 (M.op x X0)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b1e18134 X0 (M.op x x)
           have i₂ := b1e118318
           grind)
        | exact superpose b1e118318 b1e18134
        | exact resolve b1e18134 b1e118318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18134 b1e118318
      have b1e123394 : ∀ X0 : G, y = (σ (k y y)) ∨ (k X0 (M.op x X0)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b1e123370 X0
           have i₂ := b1e119530
           grind)
        | exact superpose b1e119530 b1e123370
        | (have j0 := b1e123370 X0
           grind)
        | exact resolve b1e123370 b1e119530
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e123370
      have b1e123463 : ∀ X0 : G, y = (k x x) ∨ (k X0 (M.op x X0)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b1e123394 X0
           have i₂ := b1e94630
           grind)
        | exact superpose b1e94630 b1e123394
        | (have j0 := b1e123394 X0
           grind)
        | exact resolve b1e123394 b1e94630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e94630 b1e123394
      have b1e123483 : ∀ X0 : G, x = y ∨ y = (k x x) ∨ (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e123463 X0
           have i₂ := b1e119530
           grind)
        | exact superpose b1e119530 b1e123463
        | (have j0 := b1e123463 X0
           grind)
        | exact resolve b1e123463 b1e119530
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e123463
      have b1e123493 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 ∨ y = (k x x) := by
        intro X0
        first
        | (have j0 := b1e123483 X0
           grind)
        | (have r₁ := b1e123483 X0
           have r₂ := b1e93273
           grind)
        | exact resolve b1e123483 b1e93273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e123483
      have b1e129133 : (τ y) = (k x (τ (M.op x y))) ∨ y = (k x x) := by
        first
        | (have i₁ := b1e35002 (M.op x y)
           have i₂ := b1e123493 y
           grind)
        | exact superpose b1e123493 b1e35002
        | exact resolve b1e35002 b1e123493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35002 b1e123493
      have b1e129137 : (τ y) = (k x (τ y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b1e129133
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e129133
        | exact resolve b1e129133 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e129133
      have b1e129198 : x = (k x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b1e129137
           have i₂ := b1e34986
           grind)
        | exact superpose b1e34986 b1e129137
        | exact resolve b1e129137 b1e34986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34986 b1e129137
      have b1e130267 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (k x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e129198
           grind)
        | exact superpose b1e129198 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e129198
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e129198
      have b1e130278 : x = (M.op x x) ∨ y = (k x x) := by grind
      clear b1e130267
      have b1e130289 : x = y ∨ y = (k x x) := by
        first
        | (have i₁ := b1e130278
           have i₂ := b1e119530
           grind)
        | exact superpose b1e119530 b1e130278
        | exact resolve b1e130278 b1e119530
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e119530 b1e130278
      have b1e130303 : y = (k x x) := by
        first
        | (have r₁ := b1e130289
           have r₂ := b1e93273
           grind)
        | exact resolve b1e130289 b1e93273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e130289
      have b1e130734 : (σ (k y x)) = (k (k y y) y) := by
        first
        | (have i₁ := b1e37933
           have i₂ := b1e130303
           grind)
        | exact superpose b1e130303 b1e37933
        | exact resolve b1e37933 b1e130303
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37933
      have b1e130741 : x = y ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b1e112871
           have i₂ := b1e130303
           grind)
        | exact superpose b1e130303 b1e112871
        | exact resolve b1e112871 b1e130303
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e112871
      have b1e130826 : (M.op y y) = (k y y) := by
        first
        | (have r₁ := b1e130741
           have r₂ := b1e93273
           grind)
        | exact resolve b1e130741 b1e93273
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e130741
      have b1e130829 : (σ y) = (k (k y y) y) := by
        first
        | (have i₁ := b1e130734
           have i₂ := b1e4226
           grind)
        | exact superpose b1e4226 b1e130734
        | exact resolve b1e130734 b1e4226
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4226 b1e130734
      have b1e130866 : (σ y) = (k (M.op y y) y) := by
        first
        | (have i₁ := b1e130829
           have i₂ := b1e130826
           grind)
        | exact superpose b1e130826 b1e130829
        | exact resolve b1e130829 b1e130826
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e130826 b1e130829
      have b1e130894 : (σ y) = (M.op y y) := by
        first
        | (have i₁ := b1e130866
           have i₂ := b1e18987 y
           grind)
        | exact superpose b1e18987 b1e130866
        | exact resolve b1e130866 b1e18987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18987 b1e130866
      have b1e130906 : x = (M.op y y) := by
        first
        | (have i₁ := b1e130894
           have i₂ := b1e92915
           grind)
        | exact superpose b1e92915 b1e130894
        | exact resolve b1e130894 b1e92915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e92915 b1e130894
      have b1e132061 : x = (k x x) := by
        first
        | (have i₁ := b1e18981 y y
           have i₂ := b1e130906
           grind)
        | exact superpose b1e130906 b1e18981
        | exact resolve b1e18981 b1e130906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18981 b1e130906
      have b1e132078 : x = y := by
        first
        | (have i₁ := b1e132061
           have i₂ := b1e130303
           grind)
        | exact superpose b1e130303 b1e132061
        | exact resolve b1e132061 b1e130303
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e130303 b1e132061
      have b1e132139 : False := by grind
      exact b1e132139
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
        intro X0 X1 X2 X3
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x y) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e16
        | exact resolve b2e16 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
      have b2e21 : (σ x) = (k (σ x) (σ y)) := by grind
      clear b2e20
      have b2e22 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e21
        | exact resolve b2e21 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e23 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e22
           grind)
        | exact superpose b2e22 b2e11
        | exact resolve b2e11 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e24 : x = (k x y) := by
        first
        | (have i₁ := b2e23
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e23
        | exact resolve b2e23 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23
      have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (σ x) (σ y) X1
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b2e10 X3 X2 (M.op X0 x) X5
           have i₂ := b2e10 X2 X0 x X1
           grind)
        | (have i₁ := b2e10 X0 (M.op X1 X3) X0 X3
           have i₂ := b2e10 X0 X1 X2 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b2e10 X2 X0 x X4
           have i₂ := b2e10 X2 X0 x X1
           grind)
        | (have i₁ := b2e10 (M.op X1 x) X1 X2 x
           have i₂ := b2e10 (M.op X1 X2) X1 X2 x
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e10 X3 X2 X4 (M.op X0 x)
           have i₂ := b2e10 X2 X0 x X1
           grind)
        | (have i₁ := b2e10 X0 (M.op X1 X3) X2 X0
           have i₂ := b2e10 X0 X1 X2 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X0 X1 X2 x
           have i₂ := b2e10 X0 X1 X3 x
           grind)
        | (have i₁ := b2e10 (M.op X1 X2) X1 X2 X3
           have i₂ := b2e10 (M.op X1 X3) X1 X2 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k (τ X0) X1)
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e11
        | exact resolve b2e11 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
      have b2e50 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e25 X1 X0
           have i₂ := b2e14 (τ X1) X0
           grind)
        | exact superpose b2e14 b2e25
        | (have j1 := b2e14 (τ X1) X0
           grind)
        | exact resolve b2e25 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e51 : x = (M.op y x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e24
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e24
        | (have j1 := b2e14 y x
           grind)
        | exact resolve b2e24 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e52 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e22
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e22
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e22 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22
      have b2e53 : (σ x) = (σ (M.op y x)) := by
        first
        | (have r₁ := b2e52
           have r₂ := b2e17
           grind)
        | exact resolve b2e52 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e54 : x = (M.op y x) := by
        first
        | (have r₁ := b2e51
           have r₂ := b2e17
           grind)
        | exact resolve b2e51 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e56 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 y X1 x
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e10
        | exact resolve b2e10 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e57 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 x) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 y x X1
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e10
        | exact resolve b2e10 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e66 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e27 X1 X0
           grind)
        | exact superpose b2e27 b2e11
        | exact resolve b2e11 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e71 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b2e31 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e31
        | exact resolve b2e31 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e125 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X2 X5) (M.op X0 X4)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b2e10 (M.op X0 X4) X2 X3 X5
           have i₂ := b2e34 X0 X4 (M.op X2 X3) X1
           grind)
        | (have i₁ := b2e10 (M.op X0 X4) X2 X3 X5
           have i₂ := b2e34 X0 X1 (M.op X2 X3) X4
           grind)
        | exact superpose b2e34 b2e10
        | exact resolve b2e10 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e135 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 X0 X2 (σ y)
           have i₂ := b2e71 X0
           grind)
        | (have i₁ := b2e10 X0 (σ y) X2 X0
           have i₂ := b2e71 X0
           grind)
        | exact superpose b2e71 b2e10
        | exact resolve b2e10 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e142 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e18
           have i₂ := b2e71 (σ x)
           grind)
        | exact superpose b2e71 b2e18
        | exact resolve b2e18 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e179 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (σ y) X1 (σ x)
           have i₂ := b2e142
           grind)
        | exact superpose b2e142 b2e10
        | exact resolve b2e10 b2e142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e180 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (σ y) X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (σ y) (σ x) X1
           have i₂ := b2e142
           grind)
        | exact superpose b2e142 b2e10
        | exact resolve b2e10 b2e142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e208 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op (σ y) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e39 X1 X0 X2 (σ y)
           have i₂ := b2e71 X0
           grind)
        | (have i₁ := b2e39 X0 (σ y) X2 X0
           have i₂ := b2e71 X0
           grind)
        | exact superpose b2e71 b2e39
        | exact resolve b2e39 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e39
      have b2e257 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e208 X0 X1 X2
           have i₂ := b2e179 X1 X0
           grind)
        | exact superpose b2e179 b2e208
        | exact resolve b2e208 b2e179
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e179 b2e208
      have b2e276 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b2e56 X0 x
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e56
        | exact resolve b2e56 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e281 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b2e56 X0 (M.op y x)
           have i₂ := b2e56 y x
           grind)
        | exact superpose b2e56 b2e56
        | exact resolve b2e56 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e292 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X1) = (M.op X1 (M.op x X0)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b2e10 X1 X0 (M.op y x) X3
           have i₂ := b2e56 X0 x
           grind)
        | exact superpose b2e56 b2e10
        | exact resolve b2e10 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e312 : ∀ X0 X1 X3 : G, (M.op (σ y) X1) = (M.op (M.op X0 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b2e292 X0 X1 X3
           have i₂ := b2e257 x X1 X0
           grind)
        | exact superpose b2e257 b2e292
        | exact resolve b2e292 b2e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e292
      have b2e317 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e281 X0
           have i₂ := b2e257 x X0 y
           grind)
        | exact superpose b2e257 b2e281
        | exact resolve b2e281 b2e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e281
      have b2e417 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X3 X4) X0) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e13 X2 (M.op (M.op X3 X4) X0)
           have i₂ := b2e32 X3 X4 X0 X2 X1
           grind)
        | (have i₁ := b2e13 (M.op X2 x) X3
           have i₂ := b2e32 X0 X1 X2 X3 x
           grind)
        | exact superpose b2e32 b2e13
        | (have j0 := b2e13 X2 (M.op (M.op X3 X4) X0)
           grind)
        | (have r₁ := b2e13 X3 (M.op (M.op X3 x) X3)
           have r₂ := b2e32 X3 x X3 X3 x
           grind)
        | exact resolve b2e13 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e434 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (σ y) X0) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e417 X0 X1 X2 X3 X4
           have i₂ := b2e312 X3 X0 X4
           grind)
        | exact superpose b2e312 b2e417
        | (have j0 := b2e417 X0 X1 X2 X3 X4
           grind)
        | exact resolve b2e417 b2e312
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e417
      have b2e482 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op x X0) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e434 X0 X1 X2 X3 X4
           have i₂ := b2e317 X0
           grind)
        | exact superpose b2e317 b2e434
        | (have j0 := b2e434 X0 X1 X2 X3 X4
           grind)
        | exact resolve b2e434 b2e317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e434
      have b2e511 : ∀ X0 X2 X3 X4 : G, (M.op x X0) ≠ (M.op (σ y) X2) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b2e482 X0 x X2 X3 X4
           have i₂ := b2e312 X0 X2 x
           grind)
        | exact superpose b2e312 b2e482
        | (have j0 := b2e482 X0 x X2 X3 X4
           grind)
        | exact resolve b2e482 b2e312
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e482
      have b2e536 : ∀ X0 X2 X3 X4 : G, (M.op x X0) ≠ (M.op x X2) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b2e511 X0 X2 X3 X4
           have i₂ := b2e317 X2
           grind)
        | exact superpose b2e317 b2e511
        | (have j0 := b2e511 X0 X2 X3 X4
           grind)
        | (have r₁ := b2e511 X0 X0 X3 X4
           have r₂ := b2e317 X0
           grind)
        | exact resolve b2e511 b2e317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e511
      have b2e558 : ∀ X0 X2 : G, (k X2 (M.op (σ y) X0)) = X2 ∨ (M.op x X0) ≠ (M.op x X2) := by
        intro X0 X2
        first
        | (have i₁ := b2e536 X0 X2 x x
           have i₂ := b2e312 x X0 x
           grind)
        | exact superpose b2e312 b2e536
        | (have j0 := b2e536 X0 X2 x x
           grind)
        | exact resolve b2e536 b2e312
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e312 b2e536
      have b2e576 : ∀ X0 X2 : G, (M.op x X0) ≠ (M.op x X2) ∨ (k X2 (M.op x X0)) = X2 := by
        intro X0 X2
        first
        | (have i₁ := b2e558 X0 X2
           have i₂ := b2e317 X0
           grind)
        | exact superpose b2e317 b2e558
        | (have j0 := b2e558 X0 X2
           grind)
        | exact resolve b2e558 b2e317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e558
      have b2e605 : (σ y) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e276 y
           grind)
        | exact superpose b2e276 b2e19
        | exact resolve b2e19 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e606 : y ≠ (M.op y x) := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e276 y
           grind)
        | exact superpose b2e276 b2e17
        | exact resolve b2e17 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e643 : x ≠ y := by
        first
        | (have i₁ := b2e606
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e606
        | exact resolve b2e606 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e606
      have b2e644 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e605
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e605
        | exact resolve b2e605 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e605
      have b2e747 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X5 X6) (M.op X3 X4))) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b2e32 X5 X6 (M.op X3 X4) X0 X1
           have i₂ := b2e37 X3 X4 X1 X0 X2
           grind)
        | (have i₁ := b2e32 X0 X1 X2 (M.op X2 X4) X5
           have i₂ := b2e37 X0 X1 X2 (M.op X2 X5) X4
           grind)
        | exact superpose b2e37 b2e32
        | exact resolve b2e32 b2e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e785 : ∀ X0 X1 X2 X5 X6 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (σ y) (M.op X5 X6)) X0) := by
        intro X0 X1 X2 X5 X6
        first
        | (have i₁ := b2e747 X0 X1 X2 x x X5 X6
           have i₂ := b2e135 (M.op X5 X6) X0 (M.op x x)
           grind)
        | exact superpose b2e135 b2e747
        | exact resolve b2e747 b2e135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e135 b2e747
      have b2e845 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e785 X0 X1 X2 x x
           have i₂ := b2e180 X0 (M.op x x)
           grind)
        | exact superpose b2e180 b2e785
        | exact resolve b2e785 b2e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e180 b2e785
      have b2e2140 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e71 X0
           have i₂ := b2e317 X0
           grind)
        | exact superpose b2e317 b2e71
        | exact resolve b2e71 b2e317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2141 : (σ y) = (M.op x (σ x)) := by
        first
        | (have i₁ := b2e142
           have i₂ := b2e317 (σ x)
           grind)
        | exact superpose b2e317 b2e142
        | exact resolve b2e142 b2e317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e142
      have b2e4023 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e49 X0 X1
           have i₂ := b2e49 X1 X0
           grind)
        | exact superpose b2e49 b2e49
        | (have j0 := b2e49 X0 X1
           have j1 := b2e49 X0 X1
           grind)
        | exact resolve b2e49 b2e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4065 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (σ X1) (σ X0)
           have i₂ := b2e49 X0 X1
           grind)
        | exact superpose b2e49 b2e13
        | (have j0 := b2e13 (σ X1) (σ X0)
           have j1 := b2e49 X0 X1
           grind)
        | (have r₁ := b2e13 (σ X1) (σ X0)
           have r₂ := b2e49 X0 X1
           grind)
        | exact resolve b2e13 b2e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4085 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b2e49 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e4086 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e4065 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4065
      have b2e4104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e4086 X0 X1
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e4086
        | (have j0 := b2e4086 X0 X1
           grind)
        | exact resolve b2e4086 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4086
      have b2e4507 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e46 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e46
        | exact resolve b2e46 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4719 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e66 X1 X0
           have i₂ := b2e14 (σ X1) X0
           grind)
        | exact superpose b2e14 b2e66
        | (have j1 := b2e14 (σ X1) X0
           grind)
        | exact resolve b2e66 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e4936 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e32 x x X1 X0 X2
           have i₂ := b2e845 X0 (M.op x x) X1
           grind)
        | exact superpose b2e845 b2e32
        | exact resolve b2e32 b2e845
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32 b2e845
      have b2e5000 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e4936 X0 X1 X2
           have i₂ := b2e2140 X0
           grind)
        | exact superpose b2e2140 b2e4936
        | exact resolve b2e4936 b2e2140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4936
      have b2e5218 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e37 x x X1 X0 X2
           have i₂ := b2e5000 X0 (M.op x x) X1
           grind)
        | exact superpose b2e5000 b2e37
        | exact resolve b2e37 b2e5000
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e37
      have b2e12128 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have j0 := b2e576 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e576
      have b2e12185 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e12128 (M.op X0 X1)
           have i₂ := b2e5218 x X0 X1
           grind)
        | exact superpose b2e5218 b2e12128
        | exact resolve b2e12128 b2e5218
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5218
      have b2e12200 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b2e66 X0 (M.op x (σ X0))
           have i₂ := b2e12128 (σ X0)
           grind)
        | exact superpose b2e12128 b2e66
        | exact resolve b2e66 b2e12128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12128
      have b2e12203 : ∀ X0 : G, (k X0 (τ (M.op x (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e12200 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e12200
        | exact resolve b2e12200 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12200
      have b2e12554 : y = (k y (τ (M.op x x))) := by
        first
        | (have i₁ := b2e12203 y
           have i₂ := b2e2140 x
           grind)
        | exact superpose b2e2140 b2e12203
        | exact resolve b2e12203 b2e2140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12203
      have b2e25418 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e4085 (τ X0)
           have i₂ := b2e27 X0 (τ X0)
           grind)
        | exact superpose b2e27 b2e4085
        | (have j0 := b2e4085 (τ X0)
           grind)
        | exact resolve b2e4085 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e25419 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e25418 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e25418
        | (have j0 := b2e25418 X0
           grind)
        | exact resolve b2e25418 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25418
      have b2e25422 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b2e25419 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e25419
        | (have j0 := b2e25419 X0
           grind)
        | exact resolve b2e25419 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25419
      have b2e25430 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e50 X0 (σ X0)
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e50
        | exact resolve b2e50 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e25522 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e25430 X0 X1
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e25430
        | (have j0 := b2e25430 X0 X1
           grind)
        | exact resolve b2e25430 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25430
      have b2e28342 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e4104 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e4104
        | exact resolve b2e4104 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4104
      have b2e28504 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e28342 X0 X1
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e28342
        | (have j0 := b2e28342 X0 X1
           grind)
        | exact resolve b2e28342 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28342
      have b2e28545 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e28504 X0 X1
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e28504
        | (have j0 := b2e28504 X0 X1
           grind)
        | exact resolve b2e28504 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28504
      have b2e46376 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e4023 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e4023
        | exact resolve b2e4023 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e46385 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k X1 (τ X0))) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e4023 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e4023
        | (have j0 := b2e4023 X1 (τ X0)
           grind)
        | exact resolve b2e4023 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e46457 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e13 (σ X1) (σ X0)
           have i₂ := b2e4023 X1 X0
           grind)
        | exact superpose b2e4023 b2e13
        | (have j0 := b2e13 (σ X1) (σ X0)
           have j1 := b2e4023 X1 X0
           grind)
        | (have r₁ := b2e13 (σ X0) (σ X1)
           have r₂ := b2e4023 X0 X1
           grind)
        | exact resolve b2e13 b2e4023
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4023
      have b2e46553 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e46457 X0 X1
           have j1 := b2e13 (σ X1) (σ X0)
           grind)
        | (have r₁ := b2e46457 X0 X1
           have r₂ := b2e13 (σ X1) (σ X0)
           grind)
        | exact resolve b2e46457 b2e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46457
      have b2e46599 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k X1 (τ X0))) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e46385 X0 X1
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e46385
        | (have j0 := b2e46385 X0 X1
           grind)
        | exact resolve b2e46385 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46385
      have b2e46604 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e46376 X0 X1
           have i₂ := b2e27 X0 X1
           grind)
        | exact superpose b2e27 b2e46376
        | (have j0 := b2e46376 X0 X1
           grind)
        | exact resolve b2e46376 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46376
      have b2e46637 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e46553 X0 X1
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e46553
        | (have j0 := b2e46553 X0 X1
           grind)
        | exact resolve b2e46553 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46553
      have b2e46638 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b2e46637 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46637
      have b2e46669 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e46599 X0 X1
           have i₂ := b2e27 X0 X1
           grind)
        | exact superpose b2e27 b2e46599
        | (have j0 := b2e46599 X0 X1
           grind)
        | exact resolve b2e46599 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46599
      have b2e46674 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e46604 X0 X1
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e46604
        | (have j0 := b2e46604 X0 X1
           grind)
        | exact resolve b2e46604 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25 b2e46604
      have b2e46708 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b2e46669 X0 X1
           have j1 := b2e13 (σ X1) X0
           grind)
        | (have r₁ := b2e46669 X1 X1
           have r₂ := b2e13 (σ X1) X1
           grind)
        | exact resolve b2e46669 b2e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46669
      have b2e46711 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e46674 X0 X1
           have j1 := b2e13 X0 (σ X1)
           grind)
        | (have r₁ := b2e46674 X0 X1
           have r₂ := b2e13 X0 (σ X1)
           grind)
        | exact resolve b2e46674 b2e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46674
      have b2e47600 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e46638 (τ X0) (τ X1)
           have i₂ := b2e4507 X1 X0
           grind)
        | exact superpose b2e4507 b2e46638
        | (have j0 := b2e46638 (τ X0) (τ X1)
           grind)
        | exact resolve b2e46638 b2e4507
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4507 b2e46638
      have b2e47638 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e47600 X0 X1
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e47600
        | (have j0 := b2e47600 X0 X1
           grind)
        | exact resolve b2e47600 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47600
      have b2e47648 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b2e47638 X0 X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e47638
        | (have j0 := b2e47638 X0 X1
           grind)
        | exact resolve b2e47638 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47638
      have b2e47652 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e47648 X0 X1
           have i₂ := b2e27 X0 (τ X1)
           grind)
        | exact superpose b2e27 b2e47648
        | (have j0 := b2e47648 X0 X1
           grind)
        | exact resolve b2e47648 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47648
      have b2e47653 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e47652 X0 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e47652
        | (have j0 := b2e47652 X0 X1
           grind)
        | exact resolve b2e47652 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47652
      have b2e47857 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op x x) = (k (M.op x x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e47653 (M.op X0 X1) (M.op x x)
           have i₂ := b2e12185 X0 X1
           grind)
        | exact superpose b2e12185 b2e47653
        | (have j0 := b2e47653 (M.op X0 X1) (M.op x x)
           grind)
        | (have r₁ := b2e47653 (M.op X0 X1) (M.op x x)
           have r₂ := b2e12185 X0 X1
           grind)
        | exact resolve b2e47653 b2e12185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12185
      have b2e47874 : ∀ X0 X1 : G, (M.op x x) = (k (M.op x x) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e47857 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47857
      have b2e49576 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e28545 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e28545
        | exact resolve b2e28545 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28545
      have b2e50075 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e46711 X0 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e46711
        | exact resolve b2e46711 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46711
      have b2e50296 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b2e49576 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e50388 : (τ (σ y)) = (k x (τ x)) ∨ x = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e4719 x x
           have i₂ := b2e2141
           grind)
        | exact superpose b2e2141 b2e4719
        | (have j0 := b2e4719 x x
           grind)
        | exact resolve b2e4719 b2e2141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4719
      have b2e50413 : y = (k x (τ x)) ∨ x = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e50388
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e50388
        | exact resolve b2e50388 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50388
      have b2e50484 : x = (M.op x (σ x)) ∨ y = (k x (τ x)) := by
        first
        | (have i₁ := b2e50413
           have i₂ := b2e276 (σ x)
           grind)
        | exact superpose b2e276 b2e50413
        | exact resolve b2e50413 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50413
      have b2e50534 : y = (k x (τ x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e50484
           have i₂ := b2e2141
           grind)
        | exact superpose b2e2141 b2e50484
        | exact resolve b2e50484 b2e2141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50484
      have b2e50737 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (k x X0) := by
        intro X0
        first
        | (have i₁ := b2e50296 x X0
           have i₂ := b2e276 X0
           grind)
        | (have i₁ := b2e50296 X0 x
           have i₂ := b2e276 X0
           grind)
        | exact superpose b2e276 b2e50296
        | (have j0 := b2e50296 x X0
           grind)
        | exact resolve b2e50296 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e50798 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (k X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b2e50296 X0 x
           have i₂ := b2e276 X0
           grind)
        | (have i₁ := b2e50296 x X0
           have i₂ := b2e276 X0
           grind)
        | exact superpose b2e276 b2e50296
        | (have j0 := b2e50296 X0 x
           grind)
        | exact resolve b2e50296 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50296
      have b2e51000 : x ≠ (σ y) ∨ x = (k x (σ x)) := by
        first
        | (have i₁ := b2e50737 (σ x)
           have i₂ := b2e2141
           grind)
        | exact superpose b2e2141 b2e50737
        | (have j0 := b2e50737 (σ x)
           grind)
        | exact resolve b2e50737 b2e2141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50737
      have b2e52566 : (σ y) = (k (σ x) x) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e27 x x
           have i₂ := b2e50534
           grind)
        | exact superpose b2e50534 b2e27
        | exact resolve b2e27 b2e50534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e52577 : y = (M.op (τ x) x) ∨ x = y ∨ x = (σ y) := by
        first
        | (have i₁ := b2e49576 (τ x) x
           have i₂ := b2e50534
           grind)
        | exact superpose b2e50534 b2e49576
        | exact resolve b2e49576 b2e50534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49576 b2e50534
      have b2e52579 : y = (M.op (τ x) x) ∨ x = (σ y) := by
        first
        | (have r₁ := b2e52577
           have r₂ := b2e643
           grind)
        | exact resolve b2e52577 b2e643
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52577
      have b2e52587 : y = (M.op x (τ x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e52579
           have i₂ := b2e276 (τ x)
           grind)
        | exact superpose b2e276 b2e52579
        | exact resolve b2e52579 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52579
      have b2e54669 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (σ y) := by
        intro X0
        first
        | (have i₁ := b2e5000 X0 x (τ x)
           have i₂ := b2e52587
           grind)
        | exact superpose b2e52587 b2e5000
        | exact resolve b2e5000 b2e52587
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e5000 b2e52587
      have b2e58171 : (σ x) = (σ y) ∨ (M.op (σ x) x) = (k x (σ x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e46708 x x
           have i₂ := b2e52566
           grind)
        | exact superpose b2e52566 b2e46708
        | (have j0 := b2e46708 x x
           grind)
        | exact resolve b2e46708 b2e52566
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46708 b2e52566
      have b2e58186 : (M.op (σ x) x) = (k x (σ x)) ∨ x = (σ y) := by
        first
        | (have r₁ := b2e58171
           have r₂ := b2e644
           grind)
        | exact resolve b2e58171 b2e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58171
      have b2e58193 : (M.op x (σ x)) = (k x (σ x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e58186
           have i₂ := b2e276 (σ x)
           grind)
        | exact superpose b2e276 b2e58186
        | exact resolve b2e58186 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58186
      have b2e58195 : (σ y) = (k x (σ x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e58193
           have i₂ := b2e2141
           grind)
        | exact superpose b2e2141 b2e58193
        | exact resolve b2e58193 b2e2141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58193
      have b2e58648 : ∀ X0 X1 : G, (M.op y x) = (k (M.op y x) (M.op X0 X1)) ∨ x = (σ y) := by
        intro X0 X1
        first
        | (have i₁ := b2e47874 X0 X1
           have i₂ := b2e54669 x
           grind)
        | exact superpose b2e54669 b2e47874
        | exact resolve b2e47874 b2e54669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47874
      have b2e58767 : x ≠ (M.op y x) ∨ x = (k x x) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e50798 x
           have i₂ := b2e54669 x
           grind)
        | exact superpose b2e54669 b2e50798
        | (have j0 := b2e50798 x
           grind)
        | exact resolve b2e50798 b2e54669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50798 b2e54669
      have b2e58770 : x = (k x x) ∨ x = (σ y) := by
        first
        | (have r₁ := b2e58767
           have r₂ := b2e54
           grind)
        | exact resolve b2e58767 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58767
      have b2e58851 : ∀ X0 X1 : G, x = (k x (M.op X0 X1)) ∨ x = (σ y) := by
        intro X0 X1
        first
        | (have i₁ := b2e58648 X0 X1
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e58648
        | exact resolve b2e58648 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58648
      have b2e60088 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e4085 x
           have i₂ := b2e58770
           grind)
        | exact superpose b2e58770 b2e4085
        | (have j0 := b2e4085 x
           grind)
        | exact resolve b2e4085 b2e58770
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4085 b2e58770
      have b2e60097 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (σ y) := by grind
      clear b2e60088
      have b2e76118 : x = (k x (σ x)) ∨ x = (σ y) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e58851 (σ x) (σ x)
           have i₂ := b2e60097
           grind)
        | exact superpose b2e60097 b2e58851
        | exact resolve b2e58851 b2e60097
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58851 b2e60097
      have b2e76119 : x = (k x (σ x)) ∨ x = (σ y) := by grind
      clear b2e76118
      have b2e76129 : x = (k x (σ x)) := by
        first
        | (have r₁ := b2e76119
           have r₂ := b2e51000
           grind)
        | exact resolve b2e76119 b2e51000
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51000 b2e76119
      have b2e76455 : x = (σ y) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e58195
           have i₂ := b2e76129
           grind)
        | exact superpose b2e76129 b2e58195
        | exact resolve b2e58195 b2e76129
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58195 b2e76129
      have b2e76482 : x = (σ y) := by grind
      clear b2e76455
      have b2e76688 : y = (τ x) := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e76482
           grind)
        | exact superpose b2e76482 b2e11
        | exact resolve b2e11 b2e76482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e76689 : ∀ X0 : G, (σ (k y X0)) = (k x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e15 y X0
           have i₂ := b2e76482
           grind)
        | exact superpose b2e76482 b2e15
        | exact resolve b2e15 b2e76482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e76690 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) x) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 y
           have i₂ := b2e76482
           grind)
        | exact superpose b2e76482 b2e15
        | exact resolve b2e15 b2e76482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e76695 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b2e46 X0 y
           have i₂ := b2e76482
           grind)
        | exact superpose b2e76482 b2e46
        | exact resolve b2e46 b2e76482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e76704 : ∀ X0 : G, (k y (τ X0)) = (τ (k x X0)) := by
        intro X0
        first
        | (have i₁ := b2e66 y X0
           have i₂ := b2e76482
           grind)
        | exact superpose b2e76482 b2e66
        | exact resolve b2e66 b2e76482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e66
      have b2e79543 : (k x x) = (σ (k y y)) := by
        first
        | (have i₁ := b2e76689 y
           have i₂ := b2e76482
           grind)
        | exact superpose b2e76482 b2e76689
        | exact resolve b2e76689 b2e76482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e79586 : ∀ X0 : G, x ≠ (σ (k y X0)) ∨ (σ X0) = (k (σ X0) x) := by
        intro X0
        first
        | (have i₁ := b2e47653 x (σ X0)
           have i₂ := b2e76689 X0
           grind)
        | exact superpose b2e76689 b2e47653
        | (have j0 := b2e47653 x (σ X0)
           grind)
        | exact resolve b2e47653 b2e76689
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47653 b2e76689
      have b2e79589 : ∀ X0 : G, x ≠ (σ (k y X0)) ∨ (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b2e79586 X0
           have i₂ := b2e76690 X0
           grind)
        | exact superpose b2e76690 b2e79586
        | (have j0 := b2e79586 X0
           grind)
        | exact resolve b2e79586 b2e76690
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e76690 b2e79586
      have b2e79915 : (k x x) = (σ (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e25522 y y
           have i₂ := b2e79543
           grind)
        | exact superpose b2e79543 b2e25522
        | (have j0 := b2e25522 y y
           grind)
        | exact resolve b2e25522 b2e79543
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e79543
      have b2e80559 : ∀ X0 : G, (k y (τ X0)) = (τ x) ∨ (k X0 x) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e76704 X0
           have i₂ := b2e50075 X0 x
           grind)
        | exact superpose b2e50075 b2e76704
        | (have j1 := b2e50075 X0 x
           grind)
        | exact resolve b2e76704 b2e50075
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50075 b2e76704
      have b2e80654 : ∀ X0 : G, y = (k y (τ X0)) ∨ (k X0 x) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e80559 X0
           have i₂ := b2e76688
           grind)
        | exact superpose b2e76688 b2e80559
        | (have j0 := b2e80559 X0
           grind)
        | exact resolve b2e80559 b2e76688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e80559
      have b2e111304 : (M.op x x) = (k x x) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e80654 x
           have i₂ := b2e76688
           grind)
        | exact superpose b2e76688 b2e80654
        | (have j0 := b2e80654 x
           grind)
        | exact resolve b2e80654 b2e76688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e80654
      have b2e112885 : (τ (M.op x x)) = (k (τ x) y) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e76695 x
           have i₂ := b2e111304
           grind)
        | exact superpose b2e111304 b2e76695
        | exact resolve b2e76695 b2e111304
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e112911 : (τ (M.op x x)) = (k y y) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e112885
           have i₂ := b2e76688
           grind)
        | exact superpose b2e76688 b2e112885
        | exact resolve b2e112885 b2e76688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e112885
      have b2e123284 : y = (k y (k y y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e12554
           have i₂ := b2e112911
           grind)
        | exact superpose b2e112911 b2e12554
        | exact resolve b2e12554 b2e112911
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12554 b2e112911
      have b2e124138 : y = (k y (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e123284
           have i₂ := b2e14 y y
           grind)
        | exact superpose b2e14 b2e123284
        | (have j1 := b2e14 y y
           grind)
        | exact resolve b2e123284 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e123284
      have b2e124170 : y = (k y (M.op y y)) ∨ y = (M.op y y) := by grind
      clear b2e124138
      have b2e124917 : (σ y) = (σ (M.op (M.op y y) y)) ∨ (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e25522 y (M.op y y)
           have i₂ := b2e124170
           grind)
        | exact superpose b2e124170 b2e25522
        | (have j0 := b2e25522 y (M.op y y)
           grind)
        | exact resolve b2e25522 b2e124170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25522 b2e124170
      have b2e124937 : (σ y) = (σ (M.op y x)) ∨ (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e124917
           have i₂ := b2e57 y y
           grind)
        | exact superpose b2e57 b2e124917
        | exact resolve b2e124917 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e124917
      have b2e124948 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e124937
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e124937
        | exact resolve b2e124937 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53 b2e124937
      have b2e124952 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b2e124948
           have r₂ := b2e644
           grind)
        | exact resolve b2e124948 b2e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e124948
      have b2e124956 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e124952
           have i₂ := b2e56 y y
           grind)
        | exact superpose b2e56 b2e124952
        | exact resolve b2e124952 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56 b2e124952
      have b2e124960 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e124956
           have i₂ := b2e276 y
           grind)
        | exact superpose b2e276 b2e124956
        | exact resolve b2e124956 b2e276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e276 b2e124956
      have b2e124964 : x = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e124960
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e124960
        | exact resolve b2e124960 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e124960
      have b2e125198 : (σ x) = (k x x) ∨ x = y ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e79915
           have i₂ := b2e124964
           grind)
        | exact superpose b2e124964 b2e79915
        | exact resolve b2e79915 b2e124964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e79915 b2e124964
      have b2e125288 : (σ x) = (k x x) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b2e125198
           have r₂ := b2e643
           grind)
        | exact resolve b2e125198 b2e643
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e125198
      have b2e125793 : (σ x) = (M.op x x) ∨ y = (M.op y y) ∨ y = (k y y) := by
        first
        | (have i₁ := b2e125288
           have i₂ := b2e111304
           grind)
        | exact superpose b2e111304 b2e125288
        | exact resolve b2e125288 b2e111304
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e111304
      have b2e125817 : (τ (σ x)) = (k (τ x) y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e76695 x
           have i₂ := b2e125288
           grind)
        | exact superpose b2e125288 b2e76695
        | exact resolve b2e76695 b2e125288
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e76695 b2e125288
      have b2e125848 : (τ (σ x)) = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e125817
           have i₂ := b2e76688
           grind)
        | exact superpose b2e76688 b2e125817
        | exact resolve b2e125817 b2e76688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e76688 b2e125817
      have b2e125856 : (σ x) = (M.op x x) ∨ y = (M.op y y) := by
        first
        | (have j1 := b2e25422 y
           grind)
        | (have r₁ := b2e125793
           have r₂ := b2e25422 y
           grind)
        | exact resolve b2e125793 b2e25422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25422 b2e125793
      have b2e125859 : x = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e125848
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e125848
        | exact resolve b2e125848 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e125848
      have b2e126234 : x ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e79589 y
           have i₂ := b2e125859
           grind)
        | exact superpose b2e125859 b2e79589
        | exact resolve b2e79589 b2e125859
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e79589 b2e125859
      have b2e126279 : x ≠ (σ x) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b2e126234
           have r₂ := b2e644
           grind)
        | exact resolve b2e126234 b2e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e644 b2e126234
      have b2e130681 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op X0 X3)) = (M.op (M.op X0 X1) (M.op x X2)) ∨ y = (M.op y y) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e125 X0 X1 x X2 X3 x
           have i₂ := b2e125856
           grind)
        | exact superpose b2e125856 b2e125
        | exact resolve b2e125 b2e125856
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e125
      have b2e130718 : ∀ X0 X1 X3 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ x) (M.op X0 X3)) ∨ y = (M.op y y) := by
        intro X0 X1 X3
        first
        | (have i₁ := b2e130681 X0 X1 x X3
           have i₂ := b2e257 x (M.op X0 X1) x
           grind)
        | exact superpose b2e257 b2e130681
        | exact resolve b2e130681 b2e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e130681
      have b2e130757 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b2e130718 X0 X1 x
           have i₂ := b2e257 X0 (σ x) x
           grind)
        | exact superpose b2e257 b2e130718
        | exact resolve b2e130718 b2e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e130718
      have b2e130781 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op x (σ x)) ∨ y = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b2e130757 X0 X1
           have i₂ := b2e317 (σ x)
           grind)
        | exact superpose b2e317 b2e130757
        | exact resolve b2e130757 b2e317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e130757
      have b2e130792 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 X1)) ∨ y = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b2e130781 X0 X1
           have i₂ := b2e2141
           grind)
        | exact superpose b2e2141 b2e130781
        | exact resolve b2e130781 b2e2141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2141 b2e130781
      have b2e130800 : ∀ X0 X1 : G, (σ y) = (M.op x (M.op X0 X1)) ∨ y = (M.op y y) := by
        intro X0 X1
        first
        | (have i₁ := b2e130792 X0 X1
           have i₂ := b2e317 (M.op X0 X1)
           grind)
        | exact superpose b2e317 b2e130792
        | exact resolve b2e130792 b2e317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e317 b2e130792
      have b2e130808 : (σ y) = (M.op (σ y) x) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e130800 x x
           have i₂ := b2e257 x x x
           grind)
        | exact superpose b2e257 b2e130800
        | exact resolve b2e130800 b2e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e257 b2e130800
      have b2e130814 : (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e130808
           have i₂ := b2e71 x
           grind)
        | exact superpose b2e71 b2e130808
        | exact resolve b2e130808 b2e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e71 b2e130808
      have b2e130819 : (σ y) = (M.op x x) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e130814
           have i₂ := b2e2140 x
           grind)
        | exact superpose b2e2140 b2e130814
        | exact resolve b2e130814 b2e2140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2140 b2e130814
      have b2e130822 : x = (M.op x x) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e130819
           have i₂ := b2e76482
           grind)
        | exact superpose b2e76482 b2e130819
        | exact resolve b2e130819 b2e76482
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e76482 b2e130819
      have b2e132015 : x = (σ x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e125856
           have i₂ := b2e130822
           grind)
        | exact superpose b2e130822 b2e125856
        | exact resolve b2e125856 b2e130822
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e125856 b2e130822
      have b2e132125 : x = (σ x) ∨ y = (M.op y y) := by grind
      clear b2e132015
      have b2e132170 : y = (M.op y y) := by
        first
        | (have r₁ := b2e132125
           have r₂ := b2e126279
           grind)
        | exact resolve b2e132125 b2e126279
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e126279 b2e132125
      have b2e132410 : ∀ X0 : G, (M.op X0 x) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e57 X0 y
           have i₂ := b2e132170
           grind)
        | exact superpose b2e132170 b2e57
        | exact resolve b2e57 b2e132170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e134963 : x = (M.op y y) := by
        first
        | (have i₁ := b2e54
           have i₂ := b2e132410 y
           grind)
        | exact superpose b2e132410 b2e54
        | exact resolve b2e54 b2e132410
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54 b2e132410
      have b2e135102 : x = y := by
        first
        | (have i₁ := b2e134963
           have i₂ := b2e132170
           grind)
        | exact superpose b2e132170 b2e134963
        | exact resolve b2e134963 b2e132170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e132170 b2e134963
      have b2e135331 : False := by grind
      exact b2e135331
    · have b3e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
        intro X0 X1 X2 X3
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x y) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
      have b3e21 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b3e10 X3 X2 (M.op X0 x) X5
           have i₂ := b3e10 X2 X0 x X1
           grind)
        | (have i₁ := b3e10 X0 (M.op X1 X3) X0 X3
           have i₂ := b3e10 X0 X1 X2 X3
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e27 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X0 X1 X2 x
           have i₂ := b3e10 X0 X1 X3 x
           grind)
        | (have i₁ := b3e10 (M.op X1 X2) X1 X2 X3
           have i₂ := b3e10 (M.op X1 X3) X1 X2 X3
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e36 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
      have b3e37 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 (τ X1) X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e96 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X2 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e27 X3 X2 X4 (M.op X0 x)
           have i₂ := b3e10 X2 X0 x X1
           grind)
        | (have i₁ := b3e27 X0 (M.op X1 X3) X2 X0
           have i₂ := b3e10 X0 X1 X2 X3
           grind)
        | exact superpose b3e10 b3e27
        | exact resolve b3e27 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e191 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (M.op X3 X4) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e27 X2 (M.op X3 X4) X0 X5
           have i₂ := b3e21 X3 X4 X0 X2 X1
           grind)
        | (have i₁ := b3e27 (M.op X2 X5) X1 X2 X3
           have i₂ := b3e21 X0 X1 X2 (M.op X1 X2) X5
           grind)
        | exact superpose b3e21 b3e27
        | exact resolve b3e27 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27
      have b3e1027 : ∀ X0 X1 X2 X5 X6 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X5 X6)) := by
        intro X0 X1 X2 X5 X6
        first
        | (have i₁ := b3e96 x x X5 X2 X6
           have i₂ := b3e191 X0 X1 X2 x x X5
           grind)
        | (have i₁ := b3e96 X0 X1 X2 (M.op X0 X1) x
           have i₂ := b3e191 X0 X1 (M.op (M.op X0 X1) X2) x x X5
           grind)
        | exact superpose b3e191 b3e96
        | exact resolve b3e96 b3e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e96
      have b3e1028 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e21 x x X0 X2 X1
           have i₂ := b3e191 X3 X4 X2 x x X0
           grind)
        | (have i₁ := b3e21 X0 X1 X2 (M.op X0 X1) x
           have i₂ := b3e191 X0 X1 (M.op (M.op X0 X1) X2) X3 X4 x
           grind)
        | exact superpose b3e191 b3e21
        | exact resolve b3e21 b3e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21 b3e191
      have b3e2129 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e36 x y
           grind)
        | exact superpose b3e36 b3e16
        | (have j1 := b3e36 x y
           grind)
        | exact resolve b3e16 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2130 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e36 x y
           grind)
        | exact superpose b3e36 b3e18
        | (have j1 := b3e36 x y
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e36 y x
           grind)
        | exact resolve b3e18 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2166 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e36 y x
           grind)
        | exact superpose b3e36 b3e18
        | (have j1 := b3e36 y x
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e36 y x
           grind)
        | exact resolve b3e18 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e2203 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
      clear b3e2166
      have b3e2206 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e2130
           have i₂ := b3e2203
           grind)
        | exact superpose b3e2203 b3e2130
        | exact resolve b3e2130 b3e2203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2130
      have b3e2207 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e2129
           have i₂ := b3e2203
           grind)
        | exact superpose b3e2203 b3e2129
        | exact resolve b3e2129 b3e2203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2129
      have b3e2235 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ (k x y)) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1027 (σ y) (σ x) X0 X1 X2
           have i₂ := b3e2203
           grind)
        | exact superpose b3e2203 b3e1027
        | exact resolve b3e1027 b3e2203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2236 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (σ (k x y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1027 X0 X1 X2 (σ y) (σ x)
           have i₂ := b3e2203
           grind)
        | exact superpose b3e2203 b3e1027
        | exact resolve b3e1027 b3e2203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1027
      have b3e2238 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (k x y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1028 X0 X1 X2 (σ y) (σ x)
           have i₂ := b3e2203
           grind)
        | exact superpose b3e2203 b3e1028
        | exact resolve b3e1028 b3e2203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1028
      have b3e2609 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op x y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e2235 X0 X1 X2
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e2235
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e2235 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2235
      have b3e2764 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ (M.op y x)) X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e2609 X0 X1 X2
           grind)
        | (have r₁ := b3e2609 X0 X1 X2
           have r₂ := b3e17
           grind)
        | exact resolve b3e2609 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2609
      have b3e3173 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (σ (M.op y x))) ∨ y = (M.op x y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e2236 X0 X1 X2
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e2236
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e2236 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2236
      have b3e3348 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (σ (M.op y x))) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e3173 X0 X1 X2
           grind)
        | (have r₁ := b3e3173 X0 X1 X2
           have r₂ := b3e17
           grind)
        | exact resolve b3e3173 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3173
      have b3e3796 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (M.op y x)) X2) ∨ y = (M.op x y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e2238 X0 X1 X2
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e2238
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e2238 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2238
      have b3e3978 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (M.op y x)) X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e3796 X0 X1 X2
           grind)
        | (have r₁ := b3e3796 X0 X1 X2
           have r₂ := b3e17
           grind)
        | exact resolve b3e3796 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3796
      have b3e13904 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e37 X0 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e37
        | exact resolve b3e37 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37
      have b3e13990 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e13904 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e13904
        | (have j0 := b3e13904 X0 X1
           grind)
        | exact resolve b3e13904 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13904
      have b3e14721 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e2207
           have i₂ := b3e13990 y x
           grind)
        | exact superpose b3e13990 b3e2207
        | (have j1 := b3e13990 y x
           grind)
        | (have r₁ := b3e2207
           have r₂ := b3e13990 y x
           grind)
        | exact resolve b3e2207 b3e13990
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2207 b3e13990
      have b3e14722 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by grind
      clear b3e14721
      have b3e25570 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e11 (k x y)
           have i₂ := b3e14722
           grind)
        | exact superpose b3e14722 b3e11
        | exact resolve b3e11 b3e14722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14722
      have b3e25603 : x = (k x y) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e25570
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e25570
        | exact resolve b3e25570 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25570
      have b3e25842 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e14 x y
           have i₂ := b3e25603
           grind)
        | exact superpose b3e25603 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e25603
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25603
      have b3e25843 : x = (M.op y x) ∨ y = (M.op x y) := by grind
      clear b3e25842
      have b3e25846 : x = (M.op y x) := by
        first
        | (have r₁ := b3e25843
           have r₂ := b3e17
           grind)
        | exact resolve b3e25843 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25843
      have b3e26316 : x ≠ x ∨ y = (k y x) := by
        first
        | (have i₁ := b3e13 y x
           have i₂ := b3e25846
           grind)
        | exact superpose b3e25846 b3e13
        | (have j0 := b3e13 y x
           grind)
        | (have r₁ := b3e13 y x
           have r₂ := b3e25846
           grind)
        | exact resolve b3e13 b3e25846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26396 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b3e2764 X0 y x
           have i₂ := b3e25846
           grind)
        | exact superpose b3e25846 b3e2764
        | exact resolve b3e2764 b3e25846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2764
      have b3e26397 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e3348 y x x
           have i₂ := b3e25846
           grind)
        | exact superpose b3e25846 b3e3348
        | exact resolve b3e3348 b3e25846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3348
      have b3e26398 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e3978 y x x
           have i₂ := b3e25846
           grind)
        | exact superpose b3e25846 b3e3978
        | exact resolve b3e3978 b3e25846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e3978
      have b3e26407 : y = (k y x) := by grind
      clear b3e26316
      have b3e27124 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e2206
           have i₂ := b3e26407
           grind)
        | exact superpose b3e26407 b3e2206
        | exact resolve b3e2206 b3e26407
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2206 b3e26407
      have b3e27127 : (σ x) = (σ (k x y)) := by grind
      clear b3e27124
      have b3e37537 : (σ (k x y)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b3e2203
           have i₂ := b3e26397 (σ y)
           grind)
        | exact superpose b3e26397 b3e2203
        | exact resolve b3e2203 b3e26397
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2203 b3e26397
      have b3e37563 : (σ x) = (M.op x (σ y)) := by
        first
        | (have i₁ := b3e37537
           have i₂ := b3e27127
           grind)
        | exact superpose b3e27127 b3e37537
        | exact resolve b3e37537 b3e27127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27127 b3e37537
      have b3e39272 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e26396 X0
           have i₂ := b3e26398 X0
           grind)
        | exact superpose b3e26398 b3e26396
        | exact resolve b3e26396 b3e26398
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26396
      have b3e39276 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e26398 (σ y)
           grind)
        | exact superpose b3e26398 b3e16
        | exact resolve b3e16 b3e26398
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26398
      have b3e39545 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b3e39276
           have i₂ := b3e37563
           grind)
        | exact superpose b3e37563 b3e39276
        | exact resolve b3e39276 b3e37563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37563 b3e39276
      have b3e39601 : (σ x) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b3e39545
           have i₂ := b3e39272 y
           grind)
        | exact superpose b3e39272 b3e39545
        | exact resolve b3e39545 b3e39272
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39272 b3e39545
      have b3e39622 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b3e39601
           have i₂ := b3e25846
           grind)
        | exact superpose b3e25846 b3e39601
        | exact resolve b3e39601 b3e25846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25846 b3e39601
      have b3e39623 : False := by grind
      exact b3e39623

/-- `Equation53`: `x = x ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,m(X,X)) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxpxx_y_pxy_pyx_Equation53 :
    AutBox.GuardAut ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 0))) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law53 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ ((Lf 0) ⋆ (Lf 0))) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law53.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a (M.op a a) ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a a)) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a (M.op a a) = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a (M.op a a)) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x (M.op x x)) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ x))) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = X0 := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x (M.op x x)) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e22 : x = (M.op x y) := by
        first
        | (have i₁ := b0e10 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e10 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e31
           grind)
        | exact superpose b0e31 b0e16
        | exact resolve b0e16 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e35 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e33
           have i₂ := b0e22
           grind)
        | exact superpose b0e22 b0e33
        | exact resolve b0e33 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e33
      have b0e36 : False := by grind
      exact b0e36
    · have b1e10 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = X0 := by
        intro X0 X1
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op x (M.op x x)) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e21 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X1)) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 (M.op X1 (M.op X0 X1))
           have i₂ := b1e10 X0 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e22 : x = (M.op x y) := by
        first
        | (have i₁ := b1e10 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e23 : x = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b1e10 x y
           have i₂ := b1e22
           grind)
        | exact superpose b1e22 b1e10
        | exact resolve b1e10 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b1e26 : y = (M.op y x) := by
        first
        | (have i₁ := b1e10 y x
           have i₂ := b1e23
           grind)
        | exact superpose b1e23 b1e10
        | exact resolve b1e10 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23
      have b1e36 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 (M.op X1 X1)
           have i₂ := b1e14 X1 X0
           grind)
        | (have i₁ := b1e10 X0 X1
           have i₂ := b1e14 X0 (M.op X0 X1)
           grind)
        | exact superpose b1e14 b1e10
        | (have j1 := b1e14 X1 X0
           grind)
        | exact resolve b1e10 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e37 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 (σ x) X0
           grind)
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (M.op (σ x) (M.op (σ x) (σ x)))
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
      have b1e39 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) := by
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
      have b1e45 : (M.op x y) = (k x y) := by grind
      have b1e46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        grind
      have b1e47 : x = (k x y) := by
        first
        | (have i₁ := b1e45
           have i₂ := b1e22
           grind)
        | exact superpose b1e22 b1e45
        | exact resolve b1e45 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e50 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (σ (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
        intro X0
        grind
      clear b1e24
      have b1e54 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
        intro X0
        first
        | (have i₁ := b1e50 X0
           have i₂ := b1e10 (τ X0) (τ X0)
           grind)
        | exact superpose b1e10 b1e50
        | exact resolve b1e50 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e55 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e54 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e54
        | exact resolve b1e54 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e57 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e25 X0 X1
           have i₂ := b1e14 X1 (τ X0)
           grind)
        | exact superpose b1e14 b1e25
        | (have j1 := b1e14 X1 (τ X0)
           grind)
        | exact resolve b1e25 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e62 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k X0 (τ X1))
           have i₂ := b1e25 X1 X0
           grind)
        | exact superpose b1e25 b1e11
        | exact resolve b1e11 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e90 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e21 X1 X1
           have i₂ := b1e14 X1 X0
           grind)
        | (have i₁ := b1e21 X0 X1
           have i₂ := b1e14 X0 (M.op X1 (M.op X0 X1))
           grind)
        | exact superpose b1e14 b1e21
        | (have j1 := b1e14 X1 X0
           grind)
        | exact resolve b1e21 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e92 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 (M.op X1 (M.op X0 X1)) X0
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e10
        | exact resolve b1e10 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e93 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X1)) X0) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 (M.op (M.op X1 (M.op X0 X1)) X0)
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e10
        | exact resolve b1e10 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21
      have b1e109 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = (τ (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
        intro X0
        grind
      have b1e117 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
        intro X0
        first
        | (have i₁ := b1e109 X0
           have i₂ := b1e10 (σ X0) (σ X0)
           grind)
        | exact superpose b1e10 b1e109
        | exact resolve b1e109 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e109
      have b1e119 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e117 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e117
        | exact resolve b1e117 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e117
      have b1e144 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b1e37 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e37
      have b1e145 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e144
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e144
        | exact resolve b1e144 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e144
      have b1e146 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e145
           have i₂ := b1e47
           grind)
        | exact superpose b1e47 b1e145
        | exact resolve b1e145 b1e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e145
      have b1e148 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b1e10 (σ y) (σ x)
           have i₂ := b1e146
           grind)
        | exact superpose b1e146 b1e10
        | exact resolve b1e10 b1e146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e172 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b1e46 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e186 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 X0) X1)) X0) = (k X0 (M.op X1 (M.op (M.op X0 X0) X1))) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e36 (M.op X1 (M.op (M.op X0 X0) X1)) X0
           have i₂ := b1e10 (M.op X0 X0) X1
           grind)
        | exact superpose b1e10 b1e36
        | (have j0 := b1e36 (M.op X1 (M.op (M.op X0 X0) X1)) X0
           grind)
        | exact resolve b1e36 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36
      have b1e244 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))))) := by
        intro X0
        first
        | (have i₁ := b1e62 X0 (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0)))))
           have i₂ := b1e55 (σ X0)
           grind)
        | exact superpose b1e55 b1e62
        | exact resolve b1e62 b1e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e248 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))) := by
        intro X0
        first
        | (have i₁ := b1e244 X0
           have i₂ := b1e11 (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))
           grind)
        | exact superpose b1e11 b1e244
        | exact resolve b1e244 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e244
      have b1e256 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e248 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e248
        | exact resolve b1e248 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e248
      have b1e283 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 (σ X1) (σ X0)
           have i₂ := b1e39 X1 X0
           grind)
        | exact superpose b1e39 b1e10
        | (have j1 := b1e39 X1 X0
           grind)
        | exact resolve b1e10 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39
      have b1e310 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e256 X1
           have i₂ := b1e14 X1 X0
           grind)
        | (have i₁ := b1e256 X0
           have i₂ := b1e14 X0 (M.op X0 (M.op X0 X0))
           grind)
        | exact superpose b1e14 b1e256
        | (have j1 := b1e14 X1 X0
           grind)
        | exact resolve b1e256 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e256
      have b1e379 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e92 X0 X0
           have i₂ := b1e14 X0 X1
           grind)
        | (have i₁ := b1e92 X0 X1
           have i₂ := b1e14 X0 (M.op X1 (M.op X0 X1))
           grind)
        | exact superpose b1e14 b1e92
        | (have j1 := b1e14 X1 X0
           grind)
        | exact resolve b1e92 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e464 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e93 X1 X1
           have i₂ := b1e14 X1 X0
           grind)
        | (have i₁ := b1e93 X0 X1
           have i₂ := b1e14 X0 (M.op X1 (M.op X0 X1))
           grind)
        | exact superpose b1e14 b1e93
        | (have j1 := b1e14 X1 X0
           grind)
        | exact resolve b1e93 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e93
      have b1e596 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      clear b1e90
      have b1e608 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e596 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e596
      have b1e623 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e608 (σ X0)
           grind)
        | exact superpose b1e608 b1e15
        | exact resolve b1e15 b1e608
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e630 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e623 X0
           have i₂ := b1e608 X0
           grind)
        | exact superpose b1e608 b1e623
        | exact resolve b1e623 b1e608
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e608 b1e623
      have b1e644 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b1e172 (σ y) (σ x)
           have i₂ := b1e146
           grind)
        | exact superpose b1e146 b1e172
        | (have j0 := b1e172 (σ y) (σ x)
           grind)
        | exact resolve b1e172 b1e146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e146 b1e172
      have b1e657 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have j1 := b1e379 (σ x) (σ y)
           grind)
        | (have r₁ := b1e644
           have r₂ := b1e379 (σ x) (σ y)
           grind)
        | exact resolve b1e644 b1e379
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e379 b1e644
      have b1e662 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b1e657
           have i₂ := b1e15 y x
           grind)
        | exact superpose b1e15 b1e657
        | exact resolve b1e657 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e657
      have b1e686 : (σ (M.op x y)) ≠ (σ (k y x)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e662
           grind)
        | exact superpose b1e662 b1e16
        | exact resolve b1e16 b1e662
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e662
      have b1e695 : (σ x) ≠ (σ (k y x)) := by
        first
        | (have i₁ := b1e686
           have i₂ := b1e22
           grind)
        | exact superpose b1e22 b1e686
        | exact resolve b1e686 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e686
      have b1e753 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) := by
        first
        | (have i₁ := b1e695
           have i₂ := b1e310 x y
           grind)
        | exact superpose b1e310 b1e695
        | (have j1 := b1e310 x y
           grind)
        | exact resolve b1e695 b1e310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e310
      have b1e755 : (σ x) ≠ (σ x) ∨ y = (k y x) := by
        first
        | (have i₁ := b1e753
           have i₂ := b1e22
           grind)
        | exact superpose b1e22 b1e753
        | exact resolve b1e753 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22 b1e753
      have b1e756 : y = (k y x) := by grind
      clear b1e755
      have b1e833 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e695
           have i₂ := b1e756
           grind)
        | exact superpose b1e756 b1e695
        | exact resolve b1e695 b1e756
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e695 b1e756
      have b1e1097 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
        first
        | (have i₁ := b1e148
           have i₂ := b1e630 x
           grind)
        | exact superpose b1e630 b1e148
        | exact resolve b1e148 b1e630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e148
      have b1e1098 : (σ y) ≠ (M.op (σ x) (σ (M.op x x))) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e630 x
           grind)
        | exact superpose b1e630 b1e18
        | exact resolve b1e18 b1e630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1211 : (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ y))) := by
        first
        | (have i₁ := b1e10 (σ y) (σ (M.op x x))
           have i₂ := b1e1097
           grind)
        | exact superpose b1e1097 b1e10
        | exact resolve b1e10 b1e1097
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1097
      have b1e1257 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e12 X1
           have i₂ := b1e57 X1 X0
           grind)
        | exact superpose b1e57 b1e12
        | (have j1 := b1e57 X1 X0
           grind)
        | exact resolve b1e12 b1e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e57
      have b1e1684 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e119 X0
           have i₂ := b1e630 X0
           grind)
        | exact superpose b1e630 b1e119
        | exact resolve b1e119 b1e630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e119 b1e630
      have b1e3120 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
        first
        | (have i₁ := b1e10 (σ (M.op x x)) (σ y)
           have i₂ := b1e1211
           grind)
        | exact superpose b1e1211 b1e10
        | exact resolve b1e10 b1e1211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1211
      have b1e3975 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X1) (σ (k X1 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e92 (σ X0) (σ X0)
           have i₂ := b1e283 X0 X1
           grind)
        | exact superpose b1e283 b1e92
        | (have j1 := b1e283 X1 X0
           grind)
        | exact resolve b1e92 b1e283
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e92 b1e283
      have b1e16512 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 (M.op X1 X0) X0
           have i₂ := b1e464 X1 X0
           grind)
        | exact superpose b1e464 b1e10
        | (have j1 := b1e464 X1 X0
           grind)
        | exact resolve b1e10 b1e464
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e464
      have b1e22908 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) x)) ∨ (σ y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1257 x X0
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1257
        | (have j0 := b1e1257 x X0
           grind)
        | exact resolve b1e1257 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1257
      have b1e23392 : ∀ X0 : G, (M.op (τ X0) x) = (τ (k (σ x) X0)) ∨ (σ y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e11 (M.op (τ X0) x)
           have i₂ := b1e22908 X0
           grind)
        | exact superpose b1e22908 b1e11
        | (have j1 := b1e22908 X0
           grind)
        | exact resolve b1e11 b1e22908
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22908
      have b1e23525 : ∀ X0 : G, (M.op (τ X0) x) = (k x (τ X0)) ∨ (σ y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e23392 X0
           have i₂ := b1e62 x X0
           grind)
        | exact superpose b1e62 b1e23392
        | (have j0 := b1e23392 X0
           grind)
        | exact resolve b1e23392 b1e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e62 b1e23392
      have b1e23715 : x = (M.op (τ (M.op (σ x) (σ (M.op x x)))) x) ∨ (σ y) = (M.op (σ x) (σ (M.op x x))) := by
        first
        | (have i₁ := b1e1684 x
           have i₂ := b1e23525 (M.op (σ x) (σ (M.op x x)))
           grind)
        | exact superpose b1e23525 b1e1684
        | (have j1 := b1e23525 (M.op (σ x) (σ (M.op x x)))
           grind)
        | exact resolve b1e1684 b1e23525
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1684 b1e23525
      have b1e23725 : x = (M.op (τ (M.op (σ x) (σ (M.op x x)))) x) := by
        first
        | (have r₁ := b1e23715
           have r₂ := b1e1098
           grind)
        | exact resolve b1e23715 b1e1098
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1098 b1e23715
      have b1e45242 : y = (k (M.op x x) x) ∨ y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b1e16512 (M.op x x) x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16512
        | exact resolve b1e16512 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16512
      have b1e53388 : (σ x) = (M.op (σ x) (M.op (σ (M.op x x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b1e3975 x (M.op x x)
           have i₂ := b1e45242
           grind)
        | exact superpose b1e45242 b1e3975
        | (have j0 := b1e3975 x (M.op x x)
           grind)
        | exact resolve b1e3975 b1e45242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3975 b1e45242
      have b1e53561 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b1e53388
           have i₂ := b1e3120
           grind)
        | exact superpose b1e3120 b1e53388
        | exact resolve b1e53388 b1e3120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3120 b1e53388
      have b1e53562 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ y = (M.op y (M.op x x)) := by grind
      clear b1e53561
      have b1e129324 : x = (M.op (τ (σ x)) x) ∨ y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b1e23725
           have i₂ := b1e53562
           grind)
        | exact superpose b1e53562 b1e23725
        | exact resolve b1e23725 b1e53562
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23725 b1e53562
      have b1e129347 : y = (M.op y (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e129324
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e129324
        | exact resolve b1e129324 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e129324
      have b1e130243 : y = (M.op y (M.op (M.op x x) y)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e10 y (M.op x x)
           have i₂ := b1e129347
           grind)
        | exact superpose b1e129347 b1e10
        | exact resolve b1e10 b1e129347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e129347
      have b1e130685 : (M.op y x) = (k x y) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e186 x y
           have i₂ := b1e130243
           grind)
        | exact superpose b1e130243 b1e186
        | (have j0 := b1e186 x x
           grind)
        | exact resolve b1e186 b1e130243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e186 b1e130243
      have b1e130703 : x = (M.op y x) ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e130685
           have i₂ := b1e47
           grind)
        | exact superpose b1e47 b1e130685
        | exact resolve b1e130685 b1e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47 b1e130685
      have b1e130704 : x = y ∨ x = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e130703
           have i₂ := b1e26
           grind)
        | exact superpose b1e26 b1e130703
        | exact resolve b1e130703 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26 b1e130703
      have b1e130705 : x = y ∨ x = y ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e130704
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e130704
        | exact resolve b1e130704 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e130704
      have b1e130706 : x = (M.op x x) ∨ x = y := by grind
      clear b1e130705
      have b1e131812 : x = (M.op x (M.op x x)) ∨ x = y := by
        first
        | (have i₁ := b1e10 x x
           have i₂ := b1e130706
           grind)
        | exact superpose b1e130706 b1e10
        | exact resolve b1e10 b1e130706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e130706
      have b1e131894 : x = y ∨ x = y := by
        first
        | (have i₁ := b1e131812
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e131812
        | exact resolve b1e131812 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e131812
      have b1e131895 : x = y := by grind
      clear b1e131894
      have b1e131975 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e833
           have i₂ := b1e131895
           grind)
        | exact superpose b1e131895 b1e833
        | exact resolve b1e833 b1e131895
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e833 b1e131895
      have b1e132055 : False := by grind
      exact b1e132055
  · rcases eq_or_ne (M.op (σ x) (M.op (σ x) (σ x))) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = X0 := by
        intro X0 X1
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : y ≠ (M.op x (M.op x x)) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X1)) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (M.op X1 (M.op X0 X1))
           have i₂ := b2e10 X0 X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 (τ X0) X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e15
        | exact resolve b2e15 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b2e10 (σ x) (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e30 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b2e10 (σ x) (σ y)
           have i₂ := b2e27
           grind)
        | exact superpose b2e27 b2e10
        | exact resolve b2e10 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 : G, y ≠ X0 ∨ (k x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b2e17
           have i₂ := b2e14 x X0
           grind)
        | (have i₁ := b2e17
           have i₂ := b2e14 X0 (M.op x (M.op x x))
           grind)
        | exact superpose b2e14 b2e17
        | (have j1 := b2e14 x X0
           grind)
        | (have r₁ := b2e17
           have r₂ := b2e14 x y
           grind)
        | exact resolve b2e17 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) := by
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
      have b2e40 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        grind
      have b2e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b2e42 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (σ (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
        intro X0
        grind
      clear b2e21
      have b2e43 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
        intro X0
        first
        | (have i₁ := b2e42 X0
           have i₂ := b2e10 (τ X0) (τ X0)
           grind)
        | exact superpose b2e10 b2e42
        | exact resolve b2e42 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42
      have b2e44 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e41
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e41
        | exact resolve b2e41 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41
      have b2e45 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e43 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e43
        | exact resolve b2e43 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e43
      have b2e46 : (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b2e44
           have i₂ := b2e27
           grind)
        | exact superpose b2e27 b2e44
        | exact resolve b2e44 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44
      have b2e49 : (k x y) = (τ (σ x)) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e46
           grind)
        | exact superpose b2e46 b2e11
        | exact resolve b2e11 b2e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e50 : x = (k x y) := by
        first
        | (have i₁ := b2e49
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e49
        | exact resolve b2e49 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e59 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e11 (k X0 (τ X1))
           have i₂ := b2e22 X1 X0
           grind)
        | exact superpose b2e22 b2e11
        | exact resolve b2e11 b2e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22
      have b2e62 : (k x y) = (M.op y x) := by
        first
        | (have j0 := b2e34 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e63 : x = (M.op y x) := by
        first
        | (have i₁ := b2e62
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e62
        | exact resolve b2e62 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50 b2e62
      have b2e71 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e20 X1 X1
           have i₂ := b2e14 X1 X0
           grind)
        | (have i₁ := b2e20 X0 X1
           have i₂ := b2e14 X0 (M.op X1 (M.op X0 X1))
           grind)
        | exact superpose b2e14 b2e20
        | (have j1 := b2e14 X1 X0
           grind)
        | exact resolve b2e20 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e74 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X0 X1)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 (M.op X1 (M.op X0 X1)) X0
           have i₂ := b2e20 X0 X1
           grind)
        | exact superpose b2e20 b2e10
        | exact resolve b2e10 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e139 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b2e40 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e230 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e10 (σ y) (σ x)
           have i₂ := b2e30
           grind)
        | exact superpose b2e30 b2e10
        | exact resolve b2e10 b2e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30
      have b2e311 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))))) := by
        intro X0
        first
        | (have i₁ := b2e59 X0 (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0)))))
           have i₂ := b2e45 (σ X0)
           grind)
        | exact superpose b2e45 b2e59
        | exact resolve b2e59 b2e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45 b2e59
      have b2e314 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))) := by
        intro X0
        first
        | (have i₁ := b2e311 X0
           have i₂ := b2e11 (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))
           grind)
        | exact superpose b2e11 b2e311
        | exact resolve b2e311 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e311
      have b2e324 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e314 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e314
        | exact resolve b2e314 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e314
      have b2e334 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e324 X1
           have i₂ := b2e14 X1 X0
           grind)
        | (have i₁ := b2e324 X0
           have i₂ := b2e14 X0 (M.op X0 (M.op X0 X0))
           grind)
        | exact superpose b2e14 b2e324
        | (have j1 := b2e14 X1 X0
           grind)
        | exact resolve b2e324 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e324
      have b2e372 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b2e74 X0 X0
           have i₂ := b2e14 X0 X1
           grind)
        | (have i₁ := b2e74 X0 X1
           have i₂ := b2e14 X0 (M.op X1 (M.op X0 X1))
           grind)
        | exact superpose b2e14 b2e74
        | (have j1 := b2e14 X1 X0
           grind)
        | exact resolve b2e74 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e377 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e74 (σ X1) (σ X1)
           have i₂ := b2e38 X0 X1
           grind)
        | exact superpose b2e38 b2e74
        | (have j1 := b2e38 X0 X1
           grind)
        | exact resolve b2e74 b2e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e38 b2e74
      have b2e577 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      clear b2e71
      have b2e588 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e577 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e577
      have b2e602 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 X0
           have i₂ := b2e588 (σ X0)
           grind)
        | exact superpose b2e588 b2e15
        | exact resolve b2e15 b2e588
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e609 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e602 X0
           have i₂ := b2e588 X0
           grind)
        | exact superpose b2e588 b2e602
        | exact resolve b2e602 b2e588
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e588 b2e602
      have b2e624 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b2e139 (σ y) (σ x)
           have i₂ := b2e230
           grind)
        | exact superpose b2e230 b2e139
        | (have j0 := b2e139 (σ y) (σ x)
           grind)
        | exact resolve b2e139 b2e230
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e230
      have b2e625 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b2e139 y x
           have i₂ := b2e63
           grind)
        | exact superpose b2e63 b2e139
        | (have j0 := b2e139 y x
           grind)
        | exact resolve b2e139 b2e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e139
      have b2e637 : (M.op x y) = (k y x) := by
        first
        | (have j1 := b2e372 x y
           grind)
        | (have r₁ := b2e625
           have r₂ := b2e372 x y
           grind)
        | exact resolve b2e625 b2e372
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e372 b2e625
      have b2e638 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b2e624
           have i₂ := b2e27
           grind)
        | exact superpose b2e27 b2e624
        | exact resolve b2e624 b2e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27 b2e624
      have b2e643 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e638
           have i₂ := b2e15 y x
           grind)
        | exact superpose b2e15 b2e638
        | exact resolve b2e638 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e638
      have b2e647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e643
           have i₂ := b2e637
           grind)
        | exact superpose b2e637 b2e643
        | exact resolve b2e643 b2e637
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e637 b2e643
      have b2e648 : (σ x) ≠ (σ y) := by
        first
        | (have r₁ := b2e647
           have r₂ := b2e16
           grind)
        | exact resolve b2e647 b2e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e647
      have b2e835 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
        first
        | (have i₁ := b2e18
           have i₂ := b2e609 x
           grind)
        | exact superpose b2e609 b2e18
        | exact resolve b2e18 b2e609
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e609
      have b2e22297 : (σ y) = (σ (k (M.op x x) x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e377 x (M.op x x)
           have i₂ := b2e835
           grind)
        | exact superpose b2e835 b2e377
        | exact resolve b2e377 b2e835
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e377 b2e835
      have b2e22444 : (σ y) = (σ (k (M.op x x) x)) := by
        first
        | (have r₁ := b2e22297
           have r₂ := b2e648
           grind)
        | exact resolve b2e22297 b2e648
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22297
      have b2e22544 : (k (M.op x x) x) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (k (M.op x x) x)
           have i₂ := b2e22444
           grind)
        | exact superpose b2e22444 b2e11
        | exact resolve b2e11 b2e22444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22444
      have b2e22688 : y = (k (M.op x x) x) := by
        first
        | (have i₁ := b2e22544
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e22544
        | exact resolve b2e22544 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22544
      have b2e22964 : y = (M.op (M.op x x) x) ∨ y = (M.op x (M.op x x)) := by
        first
        | (have i₁ := b2e40 x (M.op x x)
           have i₂ := b2e22688
           grind)
        | exact superpose b2e22688 b2e40
        | exact resolve b2e40 b2e22688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40
      have b2e22966 : y = (M.op x (M.op x x)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e334 x (M.op x x)
           have i₂ := b2e22688
           grind)
        | exact superpose b2e22688 b2e334
        | exact resolve b2e334 b2e22688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e334 b2e22688
      have b2e22978 : y = (M.op x x) := by
        first
        | (have r₁ := b2e22966
           have r₂ := b2e17
           grind)
        | exact resolve b2e22966 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22966
      have b2e22980 : y = (M.op (M.op x x) x) := by
        first
        | (have r₁ := b2e22964
           have r₂ := b2e17
           grind)
        | exact resolve b2e22964 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22964
      have b2e22991 : y = (M.op y x) := by
        first
        | (have i₁ := b2e22980
           have i₂ := b2e22978
           grind)
        | exact superpose b2e22978 b2e22980
        | exact resolve b2e22980 b2e22978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22978 b2e22980
      have b2e23001 : x = y := by
        first
        | (have i₁ := b2e22991
           have i₂ := b2e63
           grind)
        | exact superpose b2e63 b2e22991
        | exact resolve b2e22991 b2e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e63 b2e22991
      have b2e23312 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e648
           have i₂ := b2e23001
           grind)
        | exact superpose b2e23001 b2e648
        | exact resolve b2e648 b2e23001
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e648 b2e23001
      have b2e23332 : False := by grind
      exact b2e23332
    · have b3e10 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = X0 := by
        intro X0 X1
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x (M.op x x)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b3e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b3e32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X0 (τ X1))
           have i₂ := b3e22 X1 X0
           grind)
        | exact superpose b3e22 b3e11
        | exact resolve b3e11 b3e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e37 : ∀ X0 : G, y ≠ X0 ∨ (k x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b3e17
           have i₂ := b3e14 x X0
           grind)
        | (have i₁ := b3e17
           have i₂ := b3e14 X0 (M.op x (M.op x x))
           grind)
        | exact superpose b3e14 b3e17
        | (have j1 := b3e14 x X0
           grind)
        | (have r₁ := b3e17
           have r₂ := b3e14 x y
           grind)
        | exact resolve b3e17 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X1 X1
           have i₂ := b3e14 X1 X0
           grind)
        | (have i₁ := b3e10 X0 X1
           have i₂ := b3e14 X0 (M.op X1 (M.op X0 X1))
           grind)
        | exact superpose b3e14 b3e10
        | (have j1 := b3e14 X1 X0
           grind)
        | exact resolve b3e10 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e40 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (σ x) (M.op (σ x) (σ x)))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e41 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) := by
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
      have b3e44 : (k x y) = (M.op y x) := by
        first
        | (have j0 := b3e37 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37
      have b3e46 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) = (σ (M.op (τ X0) (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
        intro X0
        grind
      clear b3e21
      have b3e47 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
        intro X0
        first
        | (have i₁ := b3e46 X0
           have i₂ := b3e10 (τ X0) (τ X0)
           grind)
        | exact superpose b3e10 b3e46
        | exact resolve b3e46 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e46
      have b3e48 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e47 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e47
        | exact resolve b3e47 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e47
      have b3e71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e22 X0 X1
           have i₂ := b3e38 (τ X0) X1
           grind)
        | exact superpose b3e38 b3e22
        | (have j1 := b3e38 (τ X0) X1
           grind)
        | exact resolve b3e22 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e22
      have b3e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e38 (σ X0) (σ X1)
           grind)
        | exact superpose b3e38 b3e15
        | (have j1 := b3e38 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38
      have b3e80 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = (τ (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
        intro X0
        grind
      have b3e88 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
        intro X0
        first
        | (have i₁ := b3e80 X0
           have i₂ := b3e10 (σ X0) (σ X0)
           grind)
        | exact superpose b3e10 b3e80
        | exact resolve b3e80 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e80
      have b3e90 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e88 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e88
        | exact resolve b3e88 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e88
      have b3e91 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b3e40 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40
      have b3e92 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e91
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e91
        | exact resolve b3e91 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e91
      have b3e93 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b3e92
           have i₂ := b3e44
           grind)
        | exact superpose b3e44 b3e92
        | exact resolve b3e92 b3e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44 b3e92
      have b3e95 : (σ y) = (M.op (σ y) (M.op (σ x) (σ (M.op y x)))) := by
        first
        | (have i₁ := b3e10 (σ y) (σ x)
           have i₂ := b3e93
           grind)
        | exact superpose b3e93 b3e10
        | exact resolve b3e10 b3e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e159 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))))) := by
        intro X0
        first
        | (have i₁ := b3e32 X0 (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0)))))
           have i₂ := b3e48 (σ X0)
           grind)
        | exact superpose b3e48 b3e32
        | exact resolve b3e32 b3e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e32 b3e48
      have b3e162 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))) := by
        intro X0
        first
        | (have i₁ := b3e159 X0
           have i₂ := b3e11 (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0))))
           grind)
        | exact superpose b3e11 b3e159
        | exact resolve b3e159 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e159
      have b3e170 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e162 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e162
        | exact resolve b3e162 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e162
      have b3e206 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e170 X1
           have i₂ := b3e14 X1 X0
           grind)
        | (have i₁ := b3e170 X0
           have i₂ := b3e14 X0 (M.op X0 (M.op X0 X0))
           grind)
        | exact superpose b3e14 b3e170
        | (have j1 := b3e14 X1 X0
           grind)
        | exact resolve b3e170 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e170
      have b3e282 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b3e206 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e813 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e90 X1
           have i₂ := b3e41 X0 X1
           grind)
        | exact superpose b3e41 b3e90
        | (have j1 := b3e41 X0 X1
           grind)
        | exact resolve b3e90 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e41 b3e90
      have b3e854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e813 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e813
        | (have j0 := b3e813 X0 X1
           grind)
        | exact resolve b3e813 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e813
      have b3e1072 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e71 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e71
        | exact resolve b3e71 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71
      have b3e1125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1072 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e1072
        | (have j0 := b3e1072 X0 X1
           grind)
        | exact resolve b3e1072 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1072
      have b3e1595 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op y x)) := by
        first
        | (have i₁ := b3e93
           have i₂ := b3e72 x y
           grind)
        | exact superpose b3e72 b3e93
        | (have j1 := b3e72 x y
           grind)
        | exact resolve b3e93 b3e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e72 b3e93
      have b3e4345 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e854 x y
           grind)
        | exact superpose b3e854 b3e16
        | (have j1 := b3e854 x y
           grind)
        | exact resolve b3e16 b3e854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e854
      have b3e4764 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
        first
        | (have i₁ := b3e4345
           have i₂ := b3e206 x y
           grind)
        | exact superpose b3e206 b3e4345
        | (have j1 := b3e206 x y
           grind)
        | exact resolve b3e4345 b3e206
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e206 b3e4345
      have b3e4770 : y = (M.op x y) ∨ y = (k y x) := by grind
      clear b3e4764
      have b3e4774 : y = (k y x) := by
        first
        | (have j1 := b3e282 y x
           grind)
        | (have r₁ := b3e4770
           have r₂ := b3e282 y x
           grind)
        | exact resolve b3e4770 b3e282
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e282 b3e4770
      have b3e5298 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e1125 x y
           have i₂ := b3e4774
           grind)
        | exact superpose b3e4774 b3e1125
        | (have j0 := b3e1125 x y
           grind)
        | exact resolve b3e1125 b3e4774
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1125
      have b3e19550 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e1595
           grind)
        | exact superpose b3e1595 b3e16
        | exact resolve b3e16 b3e1595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1595
      have b3e19578 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op y x)) := by
        first
        | (have i₁ := b3e19550
           have i₂ := b3e4774
           grind)
        | exact superpose b3e4774 b3e19550
        | exact resolve b3e19550 b3e4774
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4774 b3e19550
      have b3e19602 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y x)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e19578
           have i₂ := b3e5298
           grind)
        | exact superpose b3e5298 b3e19578
        | (have r₁ := b3e19578
           have r₂ := b3e5298
           grind)
        | exact resolve b3e19578 b3e5298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e5298 b3e19578
      have b3e19604 : (σ y) = (σ (M.op y x)) ∨ y = (M.op y x) := by grind
      clear b3e19602
      have b3e19882 : (M.op y x) = (τ (σ y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e11 (M.op y x)
           have i₂ := b3e19604
           grind)
        | exact superpose b3e19604 b3e11
        | exact resolve b3e11 b3e19604
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19604
      have b3e20014 : y = (M.op y x) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e19882
           have i₂ := b3e11 y
           grind)
        | exact superpose b3e11 b3e19882
        | exact resolve b3e19882 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19882
      have b3e20015 : y = (M.op y x) := by grind
      clear b3e20014
      have b3e20604 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b3e95
           have i₂ := b3e20015
           grind)
        | exact superpose b3e20015 b3e95
        | exact resolve b3e95 b3e20015
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e95
      have b3e20608 : y = (M.op y (M.op x y)) := by
        first
        | (have i₁ := b3e10 y x
           have i₂ := b3e20015
           grind)
        | exact superpose b3e20015 b3e10
        | exact resolve b3e10 b3e20015
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20015
      have b3e20700 : x = (M.op x y) := by
        first
        | (have i₁ := b3e10 x y
           have i₂ := b3e20608
           grind)
        | exact superpose b3e20608 b3e10
        | exact resolve b3e10 b3e20608
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20608
      have b3e21988 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e10 (σ x) (σ y)
           have i₂ := b3e20604
           grind)
        | exact superpose b3e20604 b3e10
        | exact resolve b3e10 b3e20604
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20604
      have b3e22194 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e21988
           grind)
        | exact superpose b3e21988 b3e16
        | exact resolve b3e16 b3e21988
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21988
      have b3e22224 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b3e22194
           have i₂ := b3e20700
           grind)
        | exact superpose b3e20700 b3e22194
        | exact resolve b3e22194 b3e20700
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20700 b3e22194
      have b3e22225 : False := by grind
      exact b3e22225

/-- `Equation765`: `x = y ◇ (z ◇ ((y ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation765 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law765 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law765.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op x x) := by grind
        have b0e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e22 : x = y := by
          first
          | (have i₁ := b0e18
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e18
          | exact resolve b0e18 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e29 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e17
          | exact resolve b0e17 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e30 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e29
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e29
          | exact resolve b0e29 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e29
        have b0e31 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b0e30
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e30
          | exact resolve b0e30 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e30
        have b0e32 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e31
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e31
          | exact resolve b0e31 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e22 b0e31
        have b0e33 : False := by grind
        exact b0e33
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X1 X2) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op x x) := by grind
        have b1e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b1e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e22 : x ≠ y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e20
          | exact resolve b1e20 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 x x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 (σ x) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X1 X2) X0)) (M.op X0 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X3 X1 (M.op X2 (M.op (M.op X1 X2) X0))
             have i₂ := b1e11 X0 X1 X2
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) X3) X0)) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 (M.op X3 (M.op (M.op (M.op X1 X2) X3) X0)) X1 X2
             have i₂ := b1e11 X0 (M.op X1 X2) X3
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X2)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 (M.op (M.op X2 (M.op X1 X2)) X0) X1 X2
             have i₂ := b1e11 X0 X2 (M.op X1 X2)
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X1) X0)) = (M.op x (M.op x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e34 (M.op X1 (M.op (M.op y X1) X0))
             have i₂ := b1e11 X0 y X1
             grind)
          | exact superpose b1e11 b1e34
          | exact resolve b1e34 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b1e34 (M.op (M.op x y) X0)
             have i₂ := b1e11 X0 x y
             grind)
          | exact superpose b1e11 b1e34
          | exact resolve b1e34 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e48 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X1 X2) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 (M.op X1 X2) X1 X2
             have i₂ := b1e15 (M.op X1 X2) X0
             grind)
          | (have i₁ := b1e11 X0 X1 X2
             have i₂ := b1e15 X0 (M.op (M.op X1 X2) X0)
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 (M.op X1 X2) X0
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact superpose b1e15 b1e16
          | (have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e16 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 x y
             have i₂ := b1e40 X0
             grind)
          | exact superpose b1e40 b1e11
          | exact resolve b1e11 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k X0 (τ X1))
             have i₂ := b1e27 X1 X0
             grind)
          | exact superpose b1e27 b1e12
          | exact resolve b1e12 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e75 : x = (M.op x (M.op y y)) := by
          first
          | (have i₁ := b1e55 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e55
          | exact resolve b1e55 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e86 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x (M.op y X0)) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 X1 x (M.op x (M.op y X0))
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e38
          | exact resolve b1e38 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e92 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X2) (M.op X0 X1))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X1 X2 (M.op X0 X2)
             have i₂ := b1e38 X1 X0 X2
             grind)
          | exact superpose b1e38 b1e11
          | exact resolve b1e11 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e107 : (M.op y y) = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b1e55 (M.op y y)
             have i₂ := b1e75
             grind)
          | exact superpose b1e75 b1e55
          | exact resolve b1e55 b1e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e111 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ x) X0)) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e35 (σ y)
             have i₂ := b1e15 (σ y) X0
             grind)
          | (have i₁ := b1e35 X0
             have i₂ := b1e15 X0 (M.op (σ y) X0)
             grind)
          | exact superpose b1e15 b1e35
          | (have j1 := b1e15 (σ y) X0
             grind)
          | exact resolve b1e35 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e141 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e46 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e146 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b1e38 X0 y x
             have i₂ := b1e107
             grind)
          | exact superpose b1e107 b1e38
          | exact resolve b1e38 b1e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e159 : ∀ X0 : G, (M.op y (M.op y (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 y y
             have i₂ := b1e146 X0
             grind)
          | exact superpose b1e146 b1e11
          | exact resolve b1e11 b1e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e190 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X2) (M.op X0 X1)) (M.op X1 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e36 X1 X2 (M.op X0 X2) X3
             have i₂ := b1e38 X1 X0 X2
             grind)
          | exact superpose b1e38 b1e36
          | exact resolve b1e36 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e213 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e36 X1 X0 X1 X2
             have i₂ := b1e38 (M.op X1 X2) (M.op X0 X1) X1
             grind)
          | exact superpose b1e38 b1e36
          | exact resolve b1e36 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e223 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op (M.op (M.op X1 X2) X3) X4)) (M.op X4 X0)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 (M.op (M.op X3 (M.op (M.op (M.op X1 X2) X3) X4)) (M.op X4 X0)) X1 X2
             have i₂ := b1e36 X4 (M.op X1 X2) X3 X0
             grind)
          | exact superpose b1e36 b1e11
          | exact resolve b1e11 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e230 : ∀ X0 X1 X2 : G, (M.op x (M.op x X0)) = (M.op (M.op X1 (M.op (M.op y X1) X2)) (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e34 (M.op (M.op X1 (M.op (M.op y X1) X2)) (M.op X2 X0))
             have i₂ := b1e36 X2 y X1 X0
             grind)
          | exact superpose b1e36 b1e34
          | exact resolve b1e34 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e231 : ∀ X0 X2 : G, (M.op x (M.op x X0)) = (M.op (M.op x (M.op x X2)) (M.op X2 X0)) := by
          intro X0 X2
          first
          | (have i₁ := b1e230 X0 x X2
             have i₂ := b1e39 X2 x
             grind)
          | exact superpose b1e39 b1e230
          | exact resolve b1e230 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e230
        have b1e238 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X4)) (M.op X4 X0)) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b1e223 X0 X1 X2 x X4
             have i₂ := b1e37 X4 X1 X2 x
             grind)
          | exact superpose b1e37 b1e223
          | exact resolve b1e223 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e223
        have b1e264 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e34 (M.op y (M.op y X0))
             have i₂ := b1e159 X0
             grind)
          | exact superpose b1e159 b1e34
          | exact resolve b1e34 b1e159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e275 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op (M.op (M.op X0 X1) X4) X2) X5)) = (M.op X3 (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X5)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e37 X5 X4 (M.op (M.op (M.op X0 X1) X4) X2) X3
             have i₂ := b1e37 X2 X0 X1 X4
             grind)
          | exact superpose b1e37 b1e37
          | exact resolve b1e37 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e292 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) X3)) = (M.op X2 (M.op (M.op X0 X2) X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e37 X3 X2 (M.op X0 X2) X1
             have i₂ := b1e38 X1 X0 X2
             grind)
          | exact superpose b1e38 b1e37
          | exact resolve b1e37 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e297 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X0 (M.op X2 X3)) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e37 X1 X2 X3 (M.op X0 (M.op X2 X3))
             have i₂ := b1e38 X1 X0 (M.op X2 X3)
             grind)
          | exact superpose b1e38 b1e37
          | exact resolve b1e37 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e308 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X2 (M.op X0 X1) x
             have i₂ := b1e37 X2 X0 X1 x
             grind)
          | exact superpose b1e37 b1e11
          | exact resolve b1e11 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e310 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e38 X3 (M.op (M.op X0 X1) X2) X2
             have i₂ := b1e37 X2 X0 X1 X2
             grind)
          | exact superpose b1e37 b1e38
          | exact resolve b1e38 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e313 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op (M.op (M.op (M.op X0 X1) X3) X2) (M.op X0 (M.op X1 X2))) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e38 X4 X3 (M.op (M.op (M.op X0 X1) X3) X2)
             have i₂ := b1e37 X2 X0 X1 X3
             grind)
          | exact superpose b1e37 b1e38
          | exact resolve b1e38 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e319 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X3 X4)) X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 (M.op (M.op (M.op X0 X1) (M.op X3 X4)) X2) X3 X4
             have i₂ := b1e37 X2 X0 X1 (M.op X3 X4)
             grind)
          | exact superpose b1e37 b1e11
          | exact resolve b1e11 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e330 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X0 (M.op (M.op X1 X2) (M.op (M.op (M.op X0 X1) X3) (M.op X2 X4)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e313 X0 X1 X2 X3 X4
             have i₂ := b1e319 (M.op (M.op X0 X1) X3) X2 X4 X0 (M.op X1 X2)
             grind)
          | exact superpose b1e319 b1e313
          | exact resolve b1e313 b1e319
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e313
        have b1e355 : ∀ X0 X1 X2 X4 X5 : G, (M.op X4 (M.op (M.op (M.op (M.op X0 X1) X4) X2) X5)) = (M.op X0 (M.op (M.op X1 X2) X5)) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b1e275 X0 X1 X2 x X4 X5
             have i₂ := b1e37 X5 X0 (M.op X1 X2) x
             grind)
          | exact superpose b1e37 b1e275
          | exact resolve b1e275 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275
        have b1e357 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X0 (M.op (M.op X1 X2) (M.op (M.op X0 (M.op X1 X3)) (M.op X2 X4)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e330 X0 X1 X2 X3 X4
             have i₂ := b1e310 X0 X1 X3 (M.op X2 X4)
             grind)
          | exact superpose b1e310 b1e330
          | exact resolve b1e330 b1e310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e330
        have b1e363 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X5)) = (M.op X4 (M.op (M.op (M.op X0 X1) (M.op X4 X2)) X5)) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b1e355 X0 X1 X2 X4 X5
             have i₂ := b1e310 (M.op X0 X1) X4 X2 X5
             grind)
          | exact superpose b1e310 b1e355
          | exact resolve b1e355 b1e310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e355
        have b1e365 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X5)) = (M.op X4 (M.op X4 (M.op X2 (M.op X0 (M.op X1 X5))))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b1e363 X0 X1 X2 X4 X5
             have i₂ := b1e319 X0 X1 X5 X4 X2
             grind)
          | exact superpose b1e319 b1e363
          | exact resolve b1e363 b1e319
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e319 b1e363
        have b1e525 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e72
        have b1e541 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e525 X0
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e525
          | exact resolve b1e525 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e525
        have b1e570 : ∀ X0 : G, (σ X0) = (M.op (σ x) (M.op (σ x) (σ (k y X0)))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e35 (σ X0)
             have i₂ := b1e50 y X0
             grind)
          | exact superpose b1e50 b1e35
          | (have j1 := b1e50 y X0
             grind)
          | exact resolve b1e35 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e589 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ x) (σ X0))) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e35 (σ y)
             have i₂ := b1e50 y X0
             grind)
          | exact superpose b1e50 b1e35
          | (have j1 := b1e50 y X0
             grind)
          | exact resolve b1e35 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e652 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e48 X0 x x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e48
          | exact resolve b1e48 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e738 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 (M.op X1 X0)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e38 X2 (M.op X1 (M.op X1 X0)) (M.op X1 X0)
             have i₂ := b1e92 X1 X0 (M.op X1 X0)
             grind)
          | exact superpose b1e92 b1e38
          | exact resolve b1e38 b1e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e832 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op (M.op X1 X2) X0)) X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e213 X1 (M.op X2 (M.op (M.op X1 X2) X0)) X3
             have i₂ := b1e11 X0 X1 X2
             grind)
          | exact superpose b1e11 b1e213
          | exact resolve b1e213 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e852 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op (M.op y (M.op y X0)) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e213 y (M.op y (M.op y X0)) X1
             have i₂ := b1e159 X0
             grind)
          | exact superpose b1e159 b1e213
          | exact resolve b1e213 b1e159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e159
        have b1e862 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (M.op y y)) (M.op y X0))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e213 X1 (M.op y y) X0
             have i₂ := b1e146 X0
             grind)
          | exact superpose b1e146 b1e213
          | exact resolve b1e213 b1e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e146
        have b1e877 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e213 X1 (M.op X0 X1) X2
             have i₂ := b1e38 (M.op (M.op X0 X1) X2) X0 X1
             grind)
          | exact superpose b1e38 b1e213
          | exact resolve b1e213 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e213
        have b1e937 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op y X0))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e862 X0 X1
             have i₂ := b1e238 X0 X1 y y
             grind)
          | exact superpose b1e238 b1e862
          | exact resolve b1e862 b1e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e862
        have b1e941 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e852 X0 X1
             have i₂ := b1e738 X0 y X1
             grind)
          | exact superpose b1e738 b1e852
          | exact resolve b1e852 b1e738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e852
        have b1e980 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 X1 (M.op y X0) (M.op y X0)
             have i₂ := b1e937 X0 (M.op y X0)
             grind)
          | exact superpose b1e937 b1e38
          | exact resolve b1e38 b1e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e989 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X2 (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e92 X2 (M.op X2 (M.op y X0)) X1
             have i₂ := b1e937 X0 X2
             grind)
          | exact superpose b1e937 b1e92
          | exact resolve b1e92 b1e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e990 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op y X0)) (M.op X0 (M.op X1 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e92 X1 X2 (M.op X1 (M.op y X0))
             have i₂ := b1e937 X0 X1
             grind)
          | exact superpose b1e937 b1e92
          | exact resolve b1e92 b1e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92
        have b1e991 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op X1 (M.op y X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e141 X1 (M.op X1 (M.op y X0))
             have i₂ := b1e937 X0 X1
             grind)
          | exact superpose b1e937 b1e141
          | (have j0 := b1e141 X1 (M.op X1 (M.op y X0))
             grind)
          | (have r₁ := b1e141 X0 (M.op X0 (M.op y X0))
             have r₂ := b1e937 X0 X0
             grind)
          | exact resolve b1e141 b1e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141
        have b1e1002 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e35 (M.op (σ y) (M.op y X0))
             have i₂ := b1e937 X0 (σ y)
             grind)
          | exact superpose b1e937 b1e35
          | exact resolve b1e35 b1e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1008 : ∀ X1 X2 : G, (M.op X1 (M.op y (M.op X1 X2))) = X2 := by
          intro X1 X2
          first
          | (have i₁ := b1e990 x X1 X2
             have i₂ := b1e238 (M.op X1 X2) X1 y x
             grind)
          | exact superpose b1e238 b1e990
          | exact resolve b1e990 b1e238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e990
        have b1e1070 : (σ x) = (M.op y (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b1e941 (σ x) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e941
          | exact resolve b1e941 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1086 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e941 (σ x) (M.op (σ y) X0)
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e941
          | exact resolve b1e941 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e1230 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op y (M.op (M.op X1 X2) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e941 (M.op X1 X2) (M.op X1 (M.op X2 X0))
             have i₂ := b1e308 X1 X2 X0
             grind)
          | exact superpose b1e308 b1e941
          | exact resolve b1e941 b1e308
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e941
        have b1e1355 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y (M.op X0 (σ y))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 X1 X0 (σ y)
             have i₂ := b1e1086 (M.op X0 (σ y))
             grind)
          | exact superpose b1e1086 b1e38
          | exact resolve b1e38 b1e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e1374 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (σ y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e1355 X0 X1
             have i₂ := b1e980 (M.op X0 (σ y)) X1
             grind)
          | exact superpose b1e980 b1e1355
          | exact resolve b1e1355 b1e980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1355
        have b1e2599 : y = (k y (τ (M.op y (σ y)))) := by
          first
          | (have i₁ := b1e541 y
             have i₂ := b1e1086 (σ y)
             grind)
          | exact superpose b1e1086 b1e541
          | exact resolve b1e541 b1e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e541
        have b1e2663 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op (M.op y X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e37 X0 x (M.op y X1) X1
             have i₂ := b1e86 X1 X0
             grind)
          | exact superpose b1e86 b1e37
          | exact resolve b1e37 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86
        have b1e2739 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e2663 X0 X1
             have i₂ := b1e980 X1 X0
             grind)
          | exact superpose b1e980 b1e2663
          | exact resolve b1e2663 b1e980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2663
        have b1e3057 : y = (M.op x (M.op y y)) ∨ (M.op y (M.op y x)) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e652 (M.op y x)
             have i₂ := b1e107
             grind)
          | exact superpose b1e107 b1e652
          | (have j0 := b1e652 (M.op y x)
             grind)
          | exact resolve b1e652 b1e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3136 : x = y ∨ (M.op y (M.op y x)) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e3057
             have i₂ := b1e75
             grind)
          | exact superpose b1e75 b1e3057
          | exact resolve b1e3057 b1e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3057
        have b1e3162 : (M.op y (M.op y x)) = (k y (M.op y x)) := by
          first
          | (have r₁ := b1e3136
             have r₂ := b1e22
             grind)
          | exact resolve b1e3136 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3136
        have b1e3173 : (M.op x (M.op x x)) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e3162
             have i₂ := b1e264 x
             grind)
          | exact superpose b1e264 b1e3162
          | exact resolve b1e3162 b1e264
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e264 b1e3162
        have b1e3180 : (M.op x y) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e3173
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e3173
          | exact resolve b1e3173 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3173
        have b1e3244 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b1e937 (M.op (σ x) (σ y)) X0
             have i₂ := b1e1070
             grind)
          | exact superpose b1e1070 b1e937
          | exact resolve b1e937 b1e1070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1070
        have b1e3695 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 (M.op y X0)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e738 (M.op X1 (M.op y X0)) X1 X2
             have i₂ := b1e937 X0 X1
             grind)
          | exact superpose b1e937 b1e738
          | exact resolve b1e738 b1e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e937
        have b1e4515 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X1 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e877 X2 X1 (M.op X2 (M.op X1 X0))
             have i₂ := b1e308 X2 X1 X0
             grind)
          | exact superpose b1e308 b1e877
          | exact resolve b1e877 b1e308
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e308
        have b1e7691 : ∀ X0 X1 : G, (M.op y x) = (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 x)) (M.op y y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e190 X1 x X0 (M.op y x)
             have i₂ := b1e107
             grind)
          | exact superpose b1e107 b1e190
          | exact resolve b1e190 b1e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107 b1e190
        have b1e7899 : ∀ X0 X1 : G, (M.op y x) = (M.op X0 (M.op y (M.op (M.op (M.op X1 X0) (M.op X1 x)) y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e7691 X0 X1
             have i₂ := b1e4515 y (M.op (M.op X1 X0) (M.op X1 x)) y
             grind)
          | (have i₁ := b1e7691 X0 X1
             have i₂ := b1e4515 y y (M.op (M.op X1 X0) (M.op X1 x))
             grind)
          | exact superpose b1e4515 b1e7691
          | exact resolve b1e7691 b1e4515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7691
        have b1e8141 : ∀ X0 X1 : G, (M.op y x) = (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X1 x) y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e7899 X0 X1
             have i₂ := b1e1230 y (M.op X1 X0) (M.op X1 x)
             grind)
          | exact superpose b1e1230 b1e7899
          | exact resolve b1e7899 b1e1230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7899
        have b1e8347 : ∀ X1 : G, (M.op y x) = (M.op X1 (M.op y (M.op (M.op X1 x) y))) := by
          intro X1
          first
          | (have i₁ := b1e8141 x X1
             have i₂ := b1e989 (M.op (M.op X1 x) y) x X1
             grind)
          | exact superpose b1e989 b1e8141
          | exact resolve b1e8141 b1e989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8141
        have b1e8502 : ∀ X1 : G, (M.op y x) = (M.op X1 (M.op X1 (M.op x y))) := by
          intro X1
          first
          | (have i₁ := b1e8347 X1
             have i₂ := b1e1230 y X1 x
             grind)
          | exact superpose b1e1230 b1e8347
          | exact resolve b1e8347 b1e1230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8347
        have b1e8730 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op x (M.op (M.op (M.op X0 X1) X3) X2))) = (M.op (M.op x (M.op x X3)) (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e231 (M.op (M.op (M.op X0 X1) X3) X2) X3
             have i₂ := b1e37 X2 X0 X1 X3
             grind)
          | exact superpose b1e37 b1e231
          | exact resolve b1e231 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e231
        have b1e8930 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op x (M.op x (M.op (M.op (M.op X0 X1) X3) X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e8730 X0 X1 X2 X3
             have i₂ := b1e738 X3 x (M.op X0 (M.op X1 X2))
             grind)
          | exact superpose b1e738 b1e8730
          | exact resolve b1e8730 b1e738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8730
        have b1e9018 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op x (M.op x (M.op (M.op X0 (M.op X1 X3)) X2))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e8930 X0 X1 X2 X3
             have i₂ := b1e310 X0 X1 X3 X2
             grind)
          | exact superpose b1e310 b1e8930
          | exact resolve b1e8930 b1e310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8930
        have b1e9305 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op y X3) X0))) = (M.op (M.op X1 (M.op X2 X3)) (M.op x (M.op x X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e238 (M.op (M.op y X3) X0) X1 X2 X3
             have i₂ := b1e39 X0 X3
             grind)
          | exact superpose b1e39 b1e238
          | exact resolve b1e238 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e9306 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op (M.op (M.op X0 X1) X5) X2))) = (M.op (M.op X3 (M.op X4 X5)) (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e238 (M.op (M.op (M.op X0 X1) X5) X2) X3 X4 X5
             have i₂ := b1e37 X2 X0 X1 X5
             grind)
          | exact superpose b1e37 b1e238
          | exact resolve b1e238 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e238
        have b1e9515 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 X5)) (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 (M.op X1 X5)) X2))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e9306 X0 X1 X2 X3 X4 X5
             have i₂ := b1e310 X0 X1 X5 X2
             grind)
          | exact superpose b1e310 b1e9306
          | exact resolve b1e9306 b1e310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e310 b1e9306
        have b1e9516 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op y X3) X0))) = (M.op x (M.op (M.op X1 (M.op X2 X3)) (M.op x X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e9305 X0 X1 X2 X3
             have i₂ := b1e4515 (M.op x X0) (M.op X1 (M.op X2 X3)) x
             grind)
          | (have i₁ := b1e9305 X0 X1 X2 X3
             have i₂ := b1e4515 (M.op x X0) x (M.op X1 (M.op X2 X3))
             grind)
          | exact superpose b1e4515 b1e9305
          | exact resolve b1e9305 b1e4515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9305
        have b1e9648 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op y X3) X0))) = (M.op x (M.op x (M.op (M.op X1 (M.op X2 X3)) X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e9516 X0 X1 X2 X3
             have i₂ := b1e4515 X0 (M.op X1 (M.op X2 X3)) x
             grind)
          | (have i₁ := b1e9516 X0 X1 X2 X3
             have i₂ := b1e4515 X0 x (M.op X1 (M.op X2 X3))
             grind)
          | exact superpose b1e4515 b1e9516
          | exact resolve b1e9516 b1e4515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9516
        have b1e9726 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op y X3) X0))) = (M.op X3 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e9648 X0 X1 X2 X3
             have i₂ := b1e9018 X1 X2 X0 X3
             grind)
          | exact superpose b1e9018 b1e9648
          | exact resolve b1e9648 b1e9018
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9018 b1e9648
        have b1e9777 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X3 X0))) = (M.op X3 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e9726 X0 X1 X2 X3
             have i₂ := b1e980 X3 X0
             grind)
          | exact superpose b1e980 b1e9726
          | exact resolve b1e9726 b1e980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9726
        have b1e9819 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e2739 x X0
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e2739
          | exact resolve b1e2739 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2739
        have b1e10472 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 X3) (M.op (M.op X1 (M.op X4 X5)) X2))) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) X2))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e292 X4 X3 X5 (M.op (M.op X1 (M.op X4 X5)) X2)
             have i₂ := b1e292 X1 (M.op X4 X5) X0 X2
             grind)
          | (have i₁ := b1e292 X4 X3 X5 (M.op (M.op X1 (M.op X4 X5)) X2)
             have i₂ := b1e292 X1 X0 (M.op X4 X5) X2
             grind)
          | exact superpose b1e292 b1e292
          | exact resolve b1e292 b1e292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e10899 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 X3) (M.op (M.op X1 (M.op X4 X5)) X2))) = (M.op X5 (M.op X1 (M.op y X2))) := by
          intro X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e10472 x X1 X2 X3 X4 X5
             have i₂ := b1e989 X2 x X1
             grind)
          | exact superpose b1e989 b1e10472
          | exact resolve b1e10472 b1e989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10472
        have b1e11217 : ∀ X1 X2 X4 X5 : G, (M.op X5 (M.op X1 (M.op y X2))) = (M.op X4 (M.op y (M.op (M.op X1 (M.op X4 X5)) X2))) := by
          intro X1 X2 X4 X5
          first
          | (have i₁ := b1e10899 X1 X2 x X4 X5
             have i₂ := b1e989 (M.op (M.op X1 (M.op X4 X5)) X2) x X4
             grind)
          | exact superpose b1e989 b1e10899
          | exact resolve b1e10899 b1e989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10899
        have b1e11435 : ∀ X1 X2 X4 X5 : G, (M.op X5 (M.op X1 (M.op y X2))) = (M.op X4 (M.op X1 (M.op (M.op X4 X5) X2))) := by
          intro X1 X2 X4 X5
          first
          | (have i₁ := b1e11217 X1 X2 X4 X5
             have i₂ := b1e1230 X2 X1 (M.op X4 X5)
             grind)
          | exact superpose b1e1230 b1e11217
          | exact resolve b1e11217 b1e1230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1230 b1e11217
        have b1e11737 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op y (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e1008 x (M.op X0 x)
             have i₂ := b1e9819 X0
             grind)
          | exact superpose b1e9819 b1e1008
          | exact resolve b1e1008 b1e9819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9819
        have b1e11946 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op (M.op X1 X5) X2))) = (M.op (M.op X5 (M.op X3 X4)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e297 X5 (M.op (M.op X1 X5) X2) X3 X4
             have i₂ := b1e292 X1 X5 X0 X2
             grind)
          | (have i₁ := b1e297 X5 (M.op (M.op X1 X5) X2) X3 X4
             have i₂ := b1e292 X1 X0 X5 X2
             grind)
          | exact superpose b1e292 b1e297
          | exact resolve b1e297 b1e292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e292 b1e297
        have b1e12199 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op (M.op X1 X5) X2))) = (M.op X5 (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X0) X4)) X2))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e11946 X0 X1 X2 X3 X4 X5
             have i₂ := b1e9515 X0 (M.op X1 X0) X2 X5 X3 X4
             grind)
          | (have i₁ := b1e11946 (M.op X1 X5) X0 X2 X3 X4 X5
             have i₂ := b1e9515 X0 X1 X2 (M.op X5 (M.op X3 X4)) (M.op X1 X5) X5
             grind)
          | exact superpose b1e9515 b1e11946
          | exact resolve b1e11946 b1e9515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9515 b1e11946
        have b1e12360 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op (M.op X1 X5) X2))) = (M.op X5 (M.op X3 (M.op (M.op X1 (M.op y X4)) X2))) := by
          intro X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e12199 x X1 X2 X3 X4 X5
             have i₂ := b1e989 X4 x X1
             grind)
          | exact superpose b1e989 b1e12199
          | exact resolve b1e12199 b1e989
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e989 b1e12199
        have b1e12492 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op (M.op X1 X5) X2))) = (M.op X5 (M.op X3 (M.op (M.op X1 X4) X2))) := by
          intro X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e12360 X1 X2 X3 X4 X5
             have i₂ := b1e3695 X4 X1 X2
             grind)
          | exact superpose b1e3695 b1e12360
          | exact resolve b1e12360 b1e3695
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3695 b1e12360
        have b1e26860 : y = (M.op y x) ∨ (M.op y (M.op x y)) = (k y (M.op x y)) := by
          first
          | (have i₁ := b1e652 (M.op x y)
             have i₂ := b1e8502 x
             grind)
          | exact superpose b1e8502 b1e652
          | (have j0 := b1e652 (M.op x y)
             grind)
          | exact resolve b1e652 b1e8502
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8502
        have b1e26889 : (M.op x (M.op y y)) = (k y (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e26860
             have i₂ := b1e4515 y y x
             grind)
          | (have i₁ := b1e26860
             have i₂ := b1e4515 y x y
             grind)
          | exact superpose b1e4515 b1e26860
          | exact resolve b1e26860 b1e4515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4515 b1e26860
        have b1e27040 : x = (k y (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e26889
             have i₂ := b1e75
             grind)
          | exact superpose b1e75 b1e26889
          | exact resolve b1e26889 b1e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75 b1e26889
        have b1e47504 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e111 (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e111
          | (have j0 := b1e111 (σ x)
             grind)
          | exact resolve b1e111 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e111
        have b1e47780 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e47504
             have i₂ := b1e16 y x
             grind)
          | exact superpose b1e16 b1e47504
          | exact resolve b1e47504 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47504
        have b1e47889 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e47780
             have i₂ := b1e1086 (σ x)
             grind)
          | exact superpose b1e1086 b1e47780
          | exact resolve b1e47780 b1e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47780
        have b1e91571 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op x X1)) = (M.op X2 (M.op (M.op X3 x) (M.op (M.op X2 (M.op X3 X0)) y))) ∨ (M.op y X1) = (k y X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e357 X2 X3 x X0 (M.op x X1)
             have i₂ := b1e652 X1
             grind)
          | exact superpose b1e652 b1e357
          | (have j1 := b1e652 X1
             grind)
          | exact resolve b1e357 b1e652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e652
        have b1e92426 : ∀ X0 X1 X3 : G, (M.op X0 (M.op x X1)) = (M.op (M.op X3 X0) (M.op (M.op X3 x) (M.op y y))) ∨ (M.op y X1) = (k y X1) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e91571 X0 X1 x X3
             have i₂ := b1e11435 (M.op X3 x) y x (M.op X3 X0)
             grind)
          | exact superpose b1e11435 b1e91571
          | (have j0 := b1e91571 X0 X1 x X3
             grind)
          | exact resolve b1e91571 b1e11435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11435 b1e91571
        have b1e93245 : ∀ X0 X1 X3 : G, (M.op X0 (M.op x X1)) = (M.op y (M.op (M.op X3 X0) (M.op (M.op X3 x) y))) ∨ (M.op y X1) = (k y X1) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e92426 X0 X1 X3
             have i₂ := b1e9777 y (M.op X3 X0) (M.op X3 x) y
             grind)
          | (have i₁ := b1e92426 X0 X1 X3
             have i₂ := b1e9777 y (M.op X3 x) y (M.op X3 X0)
             grind)
          | exact superpose b1e9777 b1e92426
          | (have j0 := b1e92426 X0 X1 X3
             grind)
          | exact resolve b1e92426 b1e9777
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9777 b1e92426
        have b1e94036 : ∀ X0 X1 X3 : G, (M.op X0 (M.op x X1)) = (M.op x (M.op y (M.op (M.op X3 (M.op X3 X0)) y))) ∨ (M.op y X1) = (k y X1) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e93245 X0 X1 X3
             have i₂ := b1e12492 X3 y y (M.op X3 X0) x
             grind)
          | (have i₁ := b1e93245 X0 X1 X1
             have i₂ := b1e12492 X1 y (M.op X1 X0) x y
             grind)
          | exact superpose b1e12492 b1e93245
          | (have j0 := b1e93245 X0 X1 X3
             grind)
          | exact resolve b1e93245 b1e12492
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12492 b1e93245
        have b1e94782 : ∀ X0 X1 X3 : G, (M.op X0 (M.op x X1)) = (M.op (M.op X3 (M.op X3 X0)) x) ∨ (M.op y X1) = (k y X1) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e94036 X0 X1 X3
             have i₂ := b1e11737 (M.op X3 (M.op X3 X0))
             grind)
          | exact superpose b1e11737 b1e94036
          | (have j0 := b1e94036 X0 X1 X3
             grind)
          | exact resolve b1e94036 b1e11737
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11737 b1e94036
        have b1e95478 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) ∨ (M.op y X1) = (k y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e94782 X0 X1 x
             have i₂ := b1e738 X0 x x
             grind)
          | exact superpose b1e738 b1e94782
          | (have j0 := b1e94782 X0 X1 x
             grind)
          | exact resolve b1e94782 b1e738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94782
        have b1e99210 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X4))) = (M.op X2 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X4))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e357 X2 X2 (M.op X2 X3) X3 (M.op X0 (M.op X1 X4))
             have i₂ := b1e365 X0 X1 (M.op X2 X3) (M.op X2 (M.op X2 X3)) X4
             grind)
          | exact superpose b1e365 b1e357
          | exact resolve b1e357 b1e365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e357 b1e365
        have b1e126020 : ∀ X0 : G, (k X0 (M.op X0 (M.op y X0))) = X0 := by
          intro X0
          first
          | (have j0 := b1e991 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e991
        have b1e130529 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (M.op X0 (M.op y (M.op X0 (σ y))))) := by
          intro X0
          first
          | (have i₁ := b1e126020 (M.op X0 (σ y))
             have i₂ := b1e1374 X0 (M.op y (M.op X0 (σ y)))
             grind)
          | exact superpose b1e1374 b1e126020
          | exact resolve b1e126020 b1e1374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126020
        have b1e130607 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e130529 X0
             have i₂ := b1e1008 X0 (σ y)
             grind)
          | (have i₁ := b1e130529 X0
             have i₂ := b1e1008 x (M.op X0 (M.op y (M.op X0 (σ y))))
             grind)
          | exact superpose b1e1008 b1e130529
          | exact resolve b1e130529 b1e1008
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1008 b1e130529
        have b1e153019 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e570 (M.op x y)
             have i₂ := b1e27040
             grind)
          | exact superpose b1e27040 b1e570
          | (have j0 := b1e570 (M.op x y)
             grind)
          | exact resolve b1e570 b1e27040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e570
        have b1e153241 : (σ (M.op x y)) = (M.op (σ y) (M.op y (σ x))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e153019
             have i₂ := b1e1002 (σ x)
             grind)
          | exact superpose b1e1002 b1e153019
          | exact resolve b1e153019 b1e1002
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1002 b1e153019
        have b1e153284 : (σ (M.op x y)) = (M.op y (M.op y (σ x))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e153241
             have i₂ := b1e1086 (M.op y (σ x))
             grind)
          | exact superpose b1e1086 b1e153241
          | exact resolve b1e153241 b1e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153241
        have b1e153318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e153284
             have i₂ := b1e3244 y
             grind)
          | exact superpose b1e3244 b1e153284
          | exact resolve b1e153284 b1e3244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3244 b1e153284
        have b1e153345 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b1e153318
             have r₂ := b1e17
             grind)
          | exact resolve b1e153318 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153318
        have b1e153357 : (σ (M.op x y)) = (M.op y (σ y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e153345
             have i₂ := b1e1086 (σ y)
             grind)
          | exact superpose b1e1086 b1e153345
          | exact resolve b1e153345 b1e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153345
        have b1e512682 : (M.op x y) = (τ (M.op y (σ y))) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e12 (M.op x y)
             have i₂ := b1e153357
             grind)
          | exact superpose b1e153357 b1e12
          | exact resolve b1e12 b1e153357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153357
        have b1e512810 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (k y x) := by
          intro X0
          first
          | (have i₁ := b1e95478 X0 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e95478
          | (have j0 := b1e95478 X0 x
             grind)
          | exact resolve b1e95478 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e95478
        have b1e513163 : ∀ X0 X1 : G, y = (M.op X1 (M.op X0 (M.op (M.op X0 X1) x))) ∨ (M.op y x) = (k y x) := by
          intro X0 X1
          first
          | (have i₁ := b1e877 X0 X1 y
             have i₂ := b1e512810 (M.op X0 X1)
             grind)
          | exact superpose b1e512810 b1e877
          | exact resolve b1e877 b1e512810
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e512810
        have b1e513174 : x = y ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b1e513163 x x
             have i₂ := b1e877 x x x
             grind)
          | exact superpose b1e877 b1e513163
          | exact resolve b1e513163 b1e877
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e877 b1e513163
        have b1e513217 : (M.op y x) = (k y x) := by
          first
          | (have r₁ := b1e513174
             have r₂ := b1e22
             grind)
          | exact resolve b1e513174 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e513174
        have b1e524458 : y = (k y (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e2599
             have i₂ := b1e512682
             grind)
          | exact superpose b1e512682 b1e2599
          | exact resolve b1e2599 b1e512682
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2599 b1e512682
        have b1e524534 : x = y ∨ y = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b1e27040
             have i₂ := b1e524458
             grind)
          | exact superpose b1e524458 b1e27040
          | exact resolve b1e27040 b1e524458
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27040 b1e524458
        have b1e524535 : x = y ∨ y = (M.op y x) := by grind
        clear b1e524534
        have b1e524537 : y = (M.op y x) := by
          first
          | (have r₁ := b1e524535
             have r₂ := b1e22
             grind)
          | exact resolve b1e524535 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e524535
        have b1e525555 : (M.op x y) = (k y y) := by
          first
          | (have i₁ := b1e3180
             have i₂ := b1e524537
             grind)
          | exact superpose b1e524537 b1e3180
          | exact resolve b1e3180 b1e524537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3180
        have b1e525583 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e980 x X0
             have i₂ := b1e524537
             grind)
          | exact superpose b1e524537 b1e980
          | exact resolve b1e980 b1e524537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e980
        have b1e525735 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op (M.op x (M.op y X0)) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e832 X0 y x X1
             have i₂ := b1e524537
             grind)
          | exact superpose b1e524537 b1e832
          | exact resolve b1e832 b1e524537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e832
        have b1e525997 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e525735 X0 X1
             have i₂ := b1e99210 X0 x y X0 X1
             grind)
          | exact superpose b1e99210 b1e525735
          | exact resolve b1e525735 b1e99210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99210 b1e525735
        have b1e565582 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op y (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e47889
             grind)
          | exact superpose b1e47889 b1e17
          | exact resolve b1e17 b1e47889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e565584 : (σ y) = (k (σ y) (σ y)) ∨ (M.op y (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e130607 (σ x)
             have i₂ := b1e47889
             grind)
          | exact superpose b1e47889 b1e130607
          | exact resolve b1e130607 b1e47889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47889 b1e130607
        have b1e565587 : (σ y) = (σ (k y y)) ∨ (M.op y (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e565584
             have i₂ := b1e16 y y
             grind)
          | exact superpose b1e16 b1e565584
          | exact resolve b1e565584 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565584
        have b1e565589 : (M.op y (σ x)) = (σ (M.op y x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e565582
             have i₂ := b1e513217
             grind)
          | exact superpose b1e513217 b1e565582
          | exact resolve b1e565582 b1e513217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565582
        have b1e565592 : (σ (M.op x y)) = (σ y) ∨ (M.op y (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e565587
             have i₂ := b1e525555
             grind)
          | exact superpose b1e525555 b1e565587
          | exact resolve b1e565587 b1e525555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565587
        have b1e565593 : (σ y) = (M.op y (σ x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e565589
             have i₂ := b1e524537
             grind)
          | exact superpose b1e524537 b1e565589
          | exact resolve b1e565589 b1e524537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565589
        have b1e565595 : (M.op y (σ x)) = (σ (M.op y x)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e565592
             have i₂ := b1e513217
             grind)
          | exact superpose b1e513217 b1e565592
          | exact resolve b1e565592 b1e513217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e513217 b1e565592
        have b1e565596 : (σ y) = (M.op x (σ x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e565593
             have i₂ := b1e525583 (σ x)
             grind)
          | exact superpose b1e525583 b1e565593
          | exact resolve b1e565593 b1e525583
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565593
        have b1e565598 : (σ y) = (M.op y (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e565595
             have i₂ := b1e524537
             grind)
          | exact superpose b1e524537 b1e565595
          | exact resolve b1e565595 b1e524537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e524537 b1e565595
        have b1e565600 : (σ y) = (M.op x (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e565598
             have i₂ := b1e525583 (σ x)
             grind)
          | exact superpose b1e525583 b1e565598
          | exact resolve b1e565598 b1e525583
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565598
        have b1e565601 : (σ y) = (M.op x (σ x)) := by
          first
          | (have r₁ := b1e565600
             have r₂ := b1e565596
             grind)
          | exact resolve b1e565600 b1e565596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565596 b1e565600
        have b1e565651 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e525997 X0 (σ x)
             have i₂ := b1e565601
             grind)
          | exact superpose b1e565601 b1e525997
          | exact resolve b1e525997 b1e565601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e525997
        have b1e565713 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op x (σ y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e738 (σ x) x X0
             have i₂ := b1e565601
             grind)
          | exact superpose b1e565601 b1e738
          | exact resolve b1e738 b1e565601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e738 b1e565601
        have b1e565995 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e565713 X0
             have i₂ := b1e1374 x X0
             grind)
          | exact superpose b1e1374 b1e565713
          | exact resolve b1e565713 b1e1374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1374 b1e565713
        have b1e566917 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e565995 (σ y)
             grind)
          | exact superpose b1e565995 b1e17
          | exact resolve b1e17 b1e565995
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e565995
        have b1e577921 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e589 y
             have i₂ := b1e565651 (σ x)
             grind)
          | exact superpose b1e565651 b1e589
          | (have j0 := b1e589 y
             grind)
          | exact resolve b1e589 b1e565651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e589 b1e565651
        have b1e578133 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e577921
             have i₂ := b1e525555
             grind)
          | exact superpose b1e525555 b1e577921
          | exact resolve b1e577921 b1e525555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e525555 b1e577921
        have b1e578640 : (σ (M.op x y)) = (M.op y (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e578133
             have i₂ := b1e1086 (σ y)
             grind)
          | exact superpose b1e1086 b1e578133
          | exact resolve b1e578133 b1e1086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1086 b1e578133
        have b1e579036 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e578640
             have i₂ := b1e525583 (σ y)
             grind)
          | exact superpose b1e525583 b1e578640
          | exact resolve b1e578640 b1e525583
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e525583 b1e578640
        have b1e579330 : (σ x) = (σ y) := by
          first
          | (have r₁ := b1e579036
             have r₂ := b1e566917
             grind)
          | exact resolve b1e579036 b1e566917
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e566917 b1e579036
        have b1e579943 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e12 y
             have i₂ := b1e579330
             grind)
          | exact superpose b1e579330 b1e12
          | exact resolve b1e12 b1e579330
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e579330
        have b1e579997 : x = y := by
          first
          | (have i₁ := b1e579943
             have i₂ := b1e12 x
             grind)
          | exact superpose b1e12 b1e579943
          | exact resolve b1e579943 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e579943
        have b1e580046 : False := by grind
        exact b1e580046
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e18 : y = (M.op x x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e22 : x = y := by
          first
          | (have i₁ := b2e18
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e18
          | exact resolve b2e18 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e23 : x = (k x x) := by grind
        have b2e26 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e17
             have i₂ := b2e22
             grind)
          | exact superpose b2e22 b2e17
          | exact resolve b2e17 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e26
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e26
          | exact resolve b2e26 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact superpose b2e15 b2e16
          | (have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e16 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e384 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e41 x x
             grind)
          | exact superpose b2e41 b2e19
          | (have j1 := b2e41 x x
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e41 x y
             grind)
          | exact resolve b2e19 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e432 : (σ y) ≠ (σ (k x x)) := by
          first
          | (have r₁ := b2e384
             have r₂ := b2e27
             grind)
          | exact resolve b2e384 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e384
        have b2e439 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e432
             have i₂ := b2e23
             grind)
          | exact superpose b2e23 b2e432
          | exact resolve b2e432 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e432
        have b2e441 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e439
             have i₂ := b2e22
             grind)
          | exact superpose b2e22 b2e439
          | exact resolve b2e439 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22 b2e439
        have b2e442 : False := by grind
        exact b2e442
      · have b3e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X1 X2) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op x x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b3e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e23 : x = (k x y) := by grind
        have b3e33 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X1 X2) X0)) (M.op X0 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11 X3 X1 (M.op X2 (M.op (M.op X1 X2) X0))
             have i₂ := b3e11 X0 X1 X2
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (M.op X1 X2) X3) X0)) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11 (M.op X3 (M.op (M.op (M.op X1 X2) X3) X0)) X1 X2
             have i₂ := b3e11 X0 (M.op X1 X2) X3
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e19
             have i₂ := b3e15 (σ x) X0
             grind)
          | (have i₁ := b3e19
             have i₂ := b3e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b3e15 b3e19
          | (have j1 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e15 (σ x) (σ y)
             grind)
          | exact resolve b3e19 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e15 (σ X0) (σ X1)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X0) (σ X1)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e134 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b3e45 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e135 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e134
             have i₂ := b3e16 x y
             grind)
          | exact superpose b3e16 b3e134
          | exact resolve b3e134 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134
        have b3e136 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e135
             have i₂ := b3e23
             grind)
          | exact superpose b3e23 b3e135
          | exact resolve b3e135 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e135
        have b3e181 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op (M.op (M.op X1 X2) X3) X4)) (M.op X4 X0)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e11 (M.op (M.op X3 (M.op (M.op (M.op X1 X2) X3) X4)) (M.op X4 X0)) X1 X2
             have i₂ := b3e33 X4 (M.op X1 X2) X3 X0
             grind)
          | exact superpose b3e33 b3e11
          | exact resolve b3e11 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e192 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X4)) (M.op X4 X0)) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b3e181 X0 X1 X2 x X4
             have i₂ := b3e34 X4 X1 X2 x
             grind)
          | exact superpose b3e34 b3e181
          | exact resolve b3e181 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e181
        have b3e488 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e46 x x
             grind)
          | exact superpose b3e46 b3e19
          | (have j1 := b3e46 x x
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e46 x y
             grind)
          | exact resolve b3e19 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e7375 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e192 (σ y) X0 X1 (σ x)
             have i₂ := b3e136
             grind)
          | exact superpose b3e136 b3e192
          | exact resolve b3e192 b3e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e136 b3e192
        have b3e13772 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e488
             have i₂ := b3e15 x x
             grind)
          | exact superpose b3e15 b3e488
          | (have j1 := b3e15 (σ x) (σ x)
             grind)
          | exact resolve b3e488 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e488
        have b3e13774 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b3e13772
             have r₂ := b3e20
             grind)
          | exact resolve b3e13772 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13772
        have b3e13782 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e13774
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e13774
          | exact resolve b3e13774 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13774
        have b3e13783 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b3e13782
        have b3e13790 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e13783
             grind)
          | exact superpose b3e13783 b3e19
          | exact resolve b3e19 b3e13783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e13799 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X1) (σ x))) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 (σ x) X0 X1 (σ x)
             have i₂ := b3e13783
             grind)
          | exact superpose b3e13783 b3e33
          | exact resolve b3e33 b3e13783
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e13783
        have b3e13861 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (M.op (M.op X0 X1) (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13799 X0 X1
             have i₂ := b3e7375 X1 (M.op X0 X1)
             grind)
          | exact superpose b3e7375 b3e13799
          | exact resolve b3e13799 b3e7375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7375 b3e13799
        have b3e13892 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13861 x x
             have i₂ := b3e11 (σ y) x x
             grind)
          | exact superpose b3e11 b3e13861
          | exact resolve b3e13861 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13861
        have b3e13909 : False := by grind
        exact b3e13909
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X1 X2) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op x x) := by grind
        have b4e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b4e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e22 : x ≠ y := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e18
          | exact resolve b4e18 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b4e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e24
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e24
          | exact resolve b4e24 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e24
        have b4e30 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e25
             grind)
          | exact superpose b4e25 b4e12
          | exact resolve b4e12 b4e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e25
        have b4e31 : x = (k x y) := by
          first
          | (have i₁ := b4e30
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e30
          | exact resolve b4e30 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e30
        have b4e34 : ∀ X0 : G, (M.op x (M.op x (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b4e11 X0 x x
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e54 : x = (M.op x y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b4e31
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e31
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e31 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e31
        have b4e60 : x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b4e54
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e54
          | exact resolve b4e54 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e54
        have b4e63 : x = (M.op x y) := by
          first
          | (have r₁ := b4e60
             have r₂ := b4e22
             grind)
          | exact resolve b4e60 b4e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e60
        have b4e65 : y = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b4e34 y
             have i₂ := b4e63
             grind)
          | exact superpose b4e63 b4e34
          | exact resolve b4e34 b4e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e34 b4e63
        have b4e67 : y = (M.op x x) := by
          first
          | (have i₁ := b4e65
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e65
          | exact resolve b4e65 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e65
        have b4e68 : x = y := by
          first
          | (have i₁ := b4e67
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e67
          | exact resolve b4e67 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e67
        have b4e69 : False := by grind
        exact b4e69
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b5e18 : y ≠ (M.op x x) := by grind
        have b5e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b5e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e22 : (σ x) = (k (σ x) (σ y)) := by grind
        have b5e23 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e22
             have i₂ := b5e16 x y
             grind)
          | exact superpose b5e16 b5e22
          | exact resolve b5e22 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e22
        have b5e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 X0 X1
             have i₂ := b5e15 (σ X0) (σ X1)
             grind)
          | exact superpose b5e15 b5e16
          | (have j1 := b5e15 (σ X0) (σ X1)
             grind)
          | exact resolve b5e16 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e62 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b5e23
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e23
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e23 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e23
        have b5e63 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b5e62
             have r₂ := b5e18
             grind)
          | exact resolve b5e62 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62
        have b5e438 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e59 x x
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e59
          | exact resolve b5e59 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e59
        have b5e1526 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e12 (k x x)
             have i₂ := b5e438
             grind)
          | exact superpose b5e438 b5e12
          | exact resolve b5e12 b5e438
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e438
        have b5e1539 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e1526
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e1526
          | exact resolve b5e1526 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1526
        have b5e3619 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e15 x x
             have i₂ := b5e1539
             grind)
          | exact superpose b5e1539 b5e15
          | (have j0 := b5e15 x y
             grind)
          | exact resolve b5e15 b5e1539
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1539
        have b5e3620 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b5e3619
             have r₂ := b5e18
             grind)
          | exact resolve b5e3619 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3619
        have b5e3628 : (σ x) = (σ y) := by
          first
          | (have r₁ := b5e3620
             have r₂ := b5e20
             grind)
          | exact resolve b5e3620 b5e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3620
        have b5e3702 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b5e17
             have i₂ := b5e3628
             grind)
          | exact superpose b5e3628 b5e17
          | exact resolve b5e17 b5e3628
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e3748 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b5e3702
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e3702
          | exact resolve b5e3702 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3702
        have b5e3754 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b5e3748
             have i₂ := b5e3628
             grind)
          | exact superpose b5e3628 b5e3748
          | exact resolve b5e3748 b5e3628
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e3628 b5e3748
        have b5e3760 : False := by grind
        exact b5e3760
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : y ≠ (M.op x x) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b6e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e22 : x ≠ y := by
          first
          | (have i₁ := b6e18
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e18
          | exact resolve b6e18 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e15 (σ x) X0
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b6e15 b6e19
          | (have j1 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e19
             have r₂ := b6e15 (σ x) (σ y)
             grind)
          | exact resolve b6e19 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e140 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b6e41 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e141 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e140
             have i₂ := b6e16 x y
             grind)
          | exact superpose b6e16 b6e140
          | exact resolve b6e140 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e140
        have b6e190 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e141
             grind)
          | exact superpose b6e141 b6e17
          | exact resolve b6e17 b6e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e256 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e190
             have i₂ := b6e15 x y
             grind)
          | exact superpose b6e15 b6e190
          | (have j1 := b6e15 x y
             grind)
          | exact resolve b6e190 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e190
        have b6e257 : y = (M.op x x) := by grind
        clear b6e256
        have b6e259 : x = y := by
          first
          | (have i₁ := b6e257
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e257
          | exact resolve b6e257 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e257
        have b6e260 : False := by grind
        exact b6e260
      · have b7e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op x x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e46 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b7e19
             have i₂ := b7e15 (σ x) X0
             grind)
          | (have i₁ := b7e19
             have i₂ := b7e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b7e15 b7e19
          | (have j1 := b7e15 (σ x) X0
             grind)
          | (have r₁ := b7e19
             have r₂ := b7e15 (σ x) (σ y)
             grind)
          | exact resolve b7e19 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e125 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b7e46 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46
        have b7e126 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e125
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e125
          | exact resolve b7e125 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e125
        have b7e164 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e126
             grind)
          | exact superpose b7e126 b7e17
          | exact resolve b7e17 b7e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e126
        have b7e227 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b7e164
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e164
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e164 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e164
        have b7e228 : y = (M.op x x) := by grind
        clear b7e227
        have b7e230 : False := by grind
        exact b7e230

/-- `Equation778`: `x = y ◇ (z ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation778 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law778 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law778.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op x x) := by grind
        have b0e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e22 : x = y := by
          first
          | (have i₁ := b0e18
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e18
          | exact resolve b0e18 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e29 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e17
          | exact resolve b0e17 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e30 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e29
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e29
          | exact resolve b0e29 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e29
        have b0e31 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b0e30
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e30
          | exact resolve b0e30 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e30
        have b0e32 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e31
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e31
          | exact resolve b0e31 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e22 b0e31
        have b0e33 : False := by grind
        exact b0e33
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op x x) := by grind
        have b1e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b1e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e22 : x ≠ y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e20
          | exact resolve b1e20 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e16
          | exact resolve b1e16 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 x x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 (σ x) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
             have i₂ := b1e11 X0 X2 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 (M.op X3 (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
             have i₂ := b1e11 X0 (M.op X2 X1) X3
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
             have i₂ := b1e11 X0 X2 (M.op X2 X1)
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y x) X0) := by
          intro X0
          first
          | (have i₁ := b1e34 (M.op (M.op y x) X0)
             have i₂ := b1e11 X0 x y
             grind)
          | exact superpose b1e11 b1e34
          | exact resolve b1e34 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) (M.op x (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X1 (M.op x (M.op y X0)) x
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e11
          | exact resolve b1e11 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e48 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X2 X1) = (M.op X1 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 (M.op X2 X1) X1 X2
             have i₂ := b1e15 (M.op X2 X1) X0
             grind)
          | (have i₁ := b1e11 X0 X1 X2
             have i₂ := b1e15 X0 (M.op (M.op X2 X1) X0)
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 (M.op X2 X1) X0
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact superpose b1e15 b1e16
          | (have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e16 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 x y
             have i₂ := b1e40 X0
             grind)
          | exact superpose b1e40 b1e11
          | exact resolve b1e11 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e73 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k X0 (τ X1))
             have i₂ := b1e27 X1 X0
             grind)
          | exact superpose b1e27 b1e12
          | exact resolve b1e12 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : x = (M.op x (M.op y y)) := by
          first
          | (have i₁ := b1e55 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e55
          | exact resolve b1e55 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e81 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e38 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
             have i₂ := b1e11 X0 X2 X1
             grind)
          | exact superpose b1e11 b1e38
          | exact resolve b1e38 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e93 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) (M.op X0 X1))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X1 X2 (M.op X2 X0)
             have i₂ := b1e38 X1 X0 X2
             grind)
          | exact superpose b1e38 b1e11
          | exact resolve b1e11 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e107 : (M.op y y) = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b1e55 (M.op y y)
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e55
          | exact resolve b1e55 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e108 : ∀ X0 : G, (M.op (M.op x x) X0) = (M.op (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b1e38 X0 (M.op y y) x
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e38
          | exact resolve b1e38 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e110 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
          intro X0
          first
          | (have i₁ := b1e108 X0
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e108
          | exact resolve b1e108 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108
        have b1e139 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e46 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e155 : ∀ X0 : G, (M.op y (M.op y (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e11 X0 y y
             have i₂ := b1e110 X0
             grind)
          | exact superpose b1e110 b1e11
          | exact resolve b1e11 b1e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110
        have b1e195 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X4 X3) X0)) = (M.op (M.op X1 (M.op (M.op X1 X2) X3)) (M.op X2 X0)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e36 X3 X1 X2 (M.op X4 (M.op (M.op X4 X3) X0))
             have i₂ := b1e11 X0 X3 X4
             grind)
          | exact superpose b1e11 b1e36
          | exact resolve b1e36 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e196 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X3)) (M.op X2 X0)) = X3 ∨ (M.op X3 X0) = (k X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e36 X3 X1 X2 X3
             have i₂ := b1e15 X3 X0
             grind)
          | (have i₁ := b1e36 X0 X1 X2 X3
             have i₂ := b1e15 X0 (M.op X0 X3)
             grind)
          | exact superpose b1e15 b1e36
          | (have j1 := b1e15 X3 X0
             grind)
          | exact resolve b1e36 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e200 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op (M.op X2 X3) (M.op (M.op X4 X0) X4))) (M.op X3 (M.op X0 X1))) = X1 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e36 (M.op (M.op X4 X0) X4) X2 X3 X1
             have i₂ := b1e38 X1 X0 X4
             grind)
          | exact superpose b1e38 b1e36
          | exact resolve b1e36 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e202 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (M.op X0 X1) (σ x))) (M.op X1 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 (σ x) X0 X1 (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e36
          | exact resolve b1e36 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e203 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (M.op X1 X2) (σ x))) (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e36 (σ x) X1 X2 (M.op (σ x) (M.op (σ y) X0))
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e36
          | exact resolve b1e36 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e207 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X0 (M.op (M.op X0 X1) x)) (M.op X1 x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 x X0 X1 (M.op y y)
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e36
          | exact resolve b1e36 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e227 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X3 (M.op (M.op X3 X1) X2)) (M.op X0 X4))) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 X4 (M.op X1 (M.op X2 X0)) (M.op X3 (M.op (M.op X3 X1) X2))
             have i₂ := b1e36 X2 X3 X1 X0
             grind)
          | exact superpose b1e36 b1e11
          | exact resolve b1e11 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e228 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X2 X1) (M.op X0 X4))) = X4 := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b1e227 X0 X1 X2 x X4
             have i₂ := b1e81 X2 x X1 (M.op X0 X4)
             grind)
          | exact superpose b1e81 b1e227
          | exact resolve b1e227 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e227
        have b1e245 : ∀ X1 : G, (M.op y y) = (M.op (M.op x X1) (M.op X1 x)) := by
          intro X1
          first
          | (have i₁ := b1e207 x X1
             have i₂ := b1e81 x x X1 (M.op X1 x)
             grind)
          | exact superpose b1e81 b1e207
          | exact resolve b1e207 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e207
        have b1e249 : ∀ X0 X2 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) X2) (M.op X2 X0)) := by
          intro X0 X2
          first
          | (have i₁ := b1e203 X0 x X2
             have i₂ := b1e81 (σ x) x X2 (M.op X2 X0)
             grind)
          | exact superpose b1e81 b1e203
          | exact resolve b1e203 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e203
        have b1e250 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) X1) (M.op X1 (σ y))) := by
          intro X1
          first
          | (have i₁ := b1e202 x X1
             have i₂ := b1e81 (σ x) x X1 (M.op X1 (σ y))
             grind)
          | exact superpose b1e81 b1e202
          | exact resolve b1e202 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e202
        have b1e252 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X4 X0) X4) X3) (M.op X3 (M.op X0 X1))) = X1 := by
          intro X0 X1 X3 X4
          first
          | (have i₁ := b1e200 X0 X1 x X3 X4
             have i₂ := b1e81 (M.op (M.op X4 X0) X4) x X3 (M.op X3 (M.op X0 X1))
             grind)
          | exact superpose b1e81 b1e200
          | exact resolve b1e200 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e200
        have b1e256 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) (M.op X2 X0)) = X3 ∨ (M.op X3 X0) = (k X3 X0) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e196 X0 x X2 X3
             have i₂ := b1e81 X3 x X2 (M.op X2 X0)
             grind)
          | exact superpose b1e81 b1e196
          | (have j0 := b1e196 X0 x X2 X3
             grind)
          | exact resolve b1e196 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e196
        have b1e257 : ∀ X0 X2 X3 X4 : G, (M.op X4 (M.op (M.op X4 X3) X0)) = (M.op (M.op X3 X2) (M.op X2 X0)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b1e195 X0 x X2 X3 X4
             have i₂ := b1e81 X3 x X2 (M.op X2 X0)
             grind)
          | exact superpose b1e81 b1e195
          | exact resolve b1e195 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81 b1e195
        have b1e283 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e250 x
             have i₂ := b1e249 (σ y) x
             grind)
          | exact superpose b1e249 b1e250
          | exact resolve b1e250 b1e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e249 b1e250
        have b1e285 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X3 (M.op X0 X1))) = X1 := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e252 X0 X1 X3 x
             have i₂ := b1e38 X3 X0 x
             grind)
          | exact superpose b1e38 b1e252
          | exact resolve b1e252 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e252
        have b1e295 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e34 (M.op y (M.op y X0))
             have i₂ := b1e155 X0
             grind)
          | exact superpose b1e155 b1e34
          | exact resolve b1e34 b1e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e155
        have b1e609 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e635 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e50 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e643 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e609 X0
             have i₂ := b1e16 X0 (k X0 X0)
             grind)
          | exact superpose b1e16 b1e609
          | (have j0 := b1e609 X0
             grind)
          | exact resolve b1e609 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e609
        have b1e688 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e48 X0 x x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e48
          | exact resolve b1e48 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e879 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op X1 (M.op (M.op X1 (σ x)) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e93 (σ x) (M.op (σ x) (M.op (σ y) X0)) X1
             have i₂ := b1e35 X0
             grind)
          | exact superpose b1e35 b1e93
          | exact resolve b1e93 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e1022 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e37 X0 (σ y) (σ y) (σ x)
             have i₂ := b1e283
             grind)
          | exact superpose b1e283 b1e37
          | exact resolve b1e37 b1e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e1032 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op X0 (σ x)) (σ x))) := by
          intro X0
          first
          | (have i₁ := b1e93 (σ x) (M.op (σ y) (σ y)) X0
             have i₂ := b1e283
             grind)
          | exact superpose b1e283 b1e93
          | exact resolve b1e93 b1e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1034 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e139 (σ x) (M.op (σ y) (σ y))
             have i₂ := b1e283
             grind)
          | exact superpose b1e283 b1e139
          | (have j0 := b1e139 (σ x) (M.op (σ y) (σ y))
             grind)
          | (have r₁ := b1e139 (σ x) (M.op (σ y) (σ y))
             have r₂ := b1e283
             grind)
          | exact resolve b1e139 b1e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e1035 : (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by grind
        clear b1e1034
        have b1e1036 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b1e1032 x
             have i₂ := b1e879 (σ x) x
             grind)
          | exact superpose b1e879 b1e1032
          | exact resolve b1e1032 b1e879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e879 b1e1032
        have b1e1278 : (τ (σ x)) = (k x (τ (M.op (σ y) (σ y)))) := by
          first
          | (have i₁ := b1e73 x (M.op (σ y) (σ y))
             have i₂ := b1e1035
             grind)
          | exact superpose b1e1035 b1e73
          | exact resolve b1e73 b1e1035
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73 b1e1035
        have b1e1282 : x = (k x (τ (M.op (σ y) (σ y)))) := by
          first
          | (have i₁ := b1e1278
             have i₂ := b1e12 x
             grind)
          | exact superpose b1e12 b1e1278
          | exact resolve b1e1278 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1278
        have b1e1360 : ∀ X0 : G, x = (k x (τ (σ X0))) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e1282
             have i₂ := b1e50 y X0
             grind)
          | exact superpose b1e50 b1e1282
          | (have j1 := b1e50 y X0
             grind)
          | exact resolve b1e1282 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50 b1e1282
        have b1e1372 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e1360 X0
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e1360
          | (have j0 := b1e1360 X0
             grind)
          | exact resolve b1e1360 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1360
        have b1e1664 : ∀ X0 : G, y = X0 ∨ (M.op (M.op x (M.op y y)) X0) = (k (M.op x (M.op y y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e15 (M.op x (M.op y y)) X0
             have i₂ := b1e41 y y
             grind)
          | exact superpose b1e41 b1e15
          | (have j0 := b1e15 (M.op x (M.op y y)) X0
             grind)
          | exact resolve b1e15 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e1690 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b1e1664 X0
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e1664
          | (have j0 := b1e1664 X0
             grind)
          | exact resolve b1e1664 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1664
        have b1e2783 : y = (M.op x (M.op y y)) ∨ (M.op y (M.op y x)) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e688 (M.op y x)
             have i₂ := b1e107
             grind)
          | exact superpose b1e107 b1e688
          | (have j0 := b1e688 (M.op y x)
             grind)
          | exact resolve b1e688 b1e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107 b1e688
        have b1e2859 : x = y ∨ (M.op y (M.op y x)) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e2783
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e2783
          | exact resolve b1e2783 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2783
        have b1e2876 : (M.op y (M.op y x)) = (k y (M.op y x)) := by
          first
          | (have r₁ := b1e2859
             have r₂ := b1e22
             grind)
          | exact resolve b1e2859 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2859
        have b1e2884 : (M.op x (M.op x x)) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e2876
             have i₂ := b1e295 x
             grind)
          | exact superpose b1e295 b1e2876
          | exact resolve b1e2876 b1e295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e295 b1e2876
        have b1e2886 : (M.op x y) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e2884
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e2884
          | exact resolve b1e2884 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2884
        have b1e7291 : ∀ X0 X1 : G, (M.op (M.op X1 (σ x)) (σ x)) = (M.op X0 (M.op (M.op X0 X1) (M.op (σ y) (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e257 (M.op (σ y) (σ y)) (σ x) X1 X0
             have i₂ := b1e283
             grind)
          | exact superpose b1e283 b1e257
          | exact resolve b1e257 b1e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e257 b1e283
        have b1e12540 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e635 (τ X0)
             have i₂ := b1e27 X0 (τ X0)
             grind)
          | exact superpose b1e27 b1e635
          | (have j0 := b1e635 (τ X0)
             grind)
          | exact resolve b1e635 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e635
        have b1e12543 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e12540 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e12540
          | (have j0 := b1e12540 X0
             grind)
          | exact resolve b1e12540 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12540
        have b1e12551 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12543 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e12543
          | (have j0 := b1e12543 X0
             grind)
          | exact resolve b1e12543 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12543
        have b1e16896 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e256 x x X0
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e256
          | (have j0 := b1e256 x x X0
             grind)
          | exact resolve b1e256 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e16943 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = (k X0 (M.op X0 X2)) ∨ X0 = X2 := by
          intro X0 X2
          first
          | (have i₁ := b1e228 X0 X0 x X2
             have i₂ := b1e256 (M.op X0 X2) (M.op x X0) X0
             grind)
          | exact superpose b1e256 b1e228
          | (have j1 := b1e256 (M.op X0 X2) X2 X0
             grind)
          | exact resolve b1e228 b1e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e228
        have b1e16949 : x = (M.op y y) ∨ (M.op x x) = (k x x) := by
          first
          | (have i₁ := b1e245 x
             have i₂ := b1e256 x x x
             grind)
          | exact superpose b1e256 b1e245
          | (have j1 := b1e256 x x x
             grind)
          | exact resolve b1e245 b1e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e256
        have b1e17100 : y = (k x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b1e16949
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e16949
          | exact resolve b1e16949 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16949
        have b1e24825 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e26 X0 (k (τ X0) (τ X0))
             have i₂ := b1e643 (τ X0)
             grind)
          | exact superpose b1e643 b1e26
          | (have j1 := b1e643 (τ X0)
             grind)
          | exact resolve b1e26 b1e643
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e643
        have b1e24860 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e24825 X0
             have i₂ := b1e27 X0 (τ X0)
             grind)
          | exact superpose b1e27 b1e24825
          | (have j0 := b1e24825 X0
             grind)
          | exact resolve b1e24825 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e24825
        have b1e24871 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e24860 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e24860
          | (have j0 := b1e24860 X0
             grind)
          | exact resolve b1e24860 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24860
        have b1e24875 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e24871 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e24871
          | (have j0 := b1e24871 X0
             grind)
          | exact resolve b1e24871 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24871
        have b1e24918 : x = (M.op x (k x x)) ∨ y = (k x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1690 (k x x)
             have i₂ := b1e24875 x
             grind)
          | exact superpose b1e24875 b1e1690
          | (have j0 := b1e1690 (k x x)
             have j1 := b1e24875 x
             grind)
          | exact resolve b1e1690 b1e24875
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1690 b1e24875
        have b1e24921 : x = (M.op x (k x x)) ∨ y = (k x x) := by
          first
          | (have r₁ := b1e24918
             have r₂ := b1e20
             grind)
          | exact resolve b1e24918 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24918
        have b1e25478 : ∀ X0 : G, (M.op (M.op x X0) (M.op X0 x)) = (k x x) ∨ y = (k x x) := by
          intro X0
          first
          | (have i₁ := b1e285 x (k x x) X0
             have i₂ := b1e24921
             grind)
          | exact superpose b1e24921 b1e285
          | exact resolve b1e285 b1e24921
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e285 b1e24921
        have b1e25494 : (M.op y y) = (k x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e25478 x
             have i₂ := b1e245 x
             grind)
          | exact superpose b1e245 b1e25478
          | exact resolve b1e25478 b1e245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e245 b1e25478
        have b1e27016 : x ≠ (M.op y y) ∨ x = (M.op x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b1e12551 x
             have i₂ := b1e25494
             grind)
          | exact superpose b1e25494 b1e12551
          | (have j0 := b1e12551 x
             grind)
          | exact resolve b1e12551 b1e25494
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12551 b1e25494
        have b1e27027 : x = (M.op x x) ∨ y = (k x x) := by
          first
          | (have r₁ := b1e27016
             have r₂ := b1e17100
             grind)
          | exact resolve b1e27016 b1e17100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17100 b1e27016
        have b1e27034 : y = (k x x) := by
          first
          | (have r₁ := b1e27027
             have r₂ := b1e20
             grind)
          | exact resolve b1e27027 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27027
        have b1e160214 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e11 y x X0
             have i₂ := b1e16896 X0
             grind)
          | exact superpose b1e16896 b1e11
          | (have j1 := b1e16896 X0
             grind)
          | exact resolve b1e11 b1e16896
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16896
        have b1e171227 : x = y ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b1e76
             have i₂ := b1e160214 y
             grind)
          | exact superpose b1e160214 b1e76
          | (have j1 := b1e160214 y
             grind)
          | exact resolve b1e76 b1e160214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e160214
        have b1e171443 : (M.op y x) = (k y x) := by
          first
          | (have r₁ := b1e171227
             have r₂ := b1e22
             grind)
          | exact resolve b1e171227 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e171227
        have b1e253962 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (k y x))) ∨ x = (k x x) := by
          first
          | (have i₁ := b1e1036
             have i₂ := b1e1372 x
             grind)
          | exact superpose b1e1372 b1e1036
          | (have j1 := b1e1372 x
             grind)
          | exact resolve b1e1036 b1e1372
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1036 b1e1372
        have b1e253993 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op y x))) ∨ x = (k x x) := by
          first
          | (have i₁ := b1e253962
             have i₂ := b1e171443
             grind)
          | exact superpose b1e171443 b1e253962
          | exact resolve b1e253962 b1e171443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e171443 b1e253962
        have b1e254001 : x = y ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op y x))) := by
          first
          | (have i₁ := b1e253993
             have i₂ := b1e27034
             grind)
          | exact superpose b1e27034 b1e253993
          | exact resolve b1e253993 b1e27034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27034 b1e253993
        have b1e254008 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op y x))) := by
          first
          | (have r₁ := b1e254001
             have r₂ := b1e22
             grind)
          | exact resolve b1e254001 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e254001
        have b1e254956 : ∀ X0 : G, (σ (M.op y x)) = (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y)))) := by
          intro X0
          first
          | (have i₁ := b1e93 (σ x) (σ (M.op y x)) X0
             have i₂ := b1e254008
             grind)
          | exact superpose b1e254008 b1e93
          | exact resolve b1e93 b1e254008
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93 b1e254008
        have b1e254987 : (M.op (M.op (σ x) (σ x)) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e254956 x
             have i₂ := b1e7291 x (σ x)
             grind)
          | exact superpose b1e7291 b1e254956
          | exact resolve b1e254956 b1e7291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7291 b1e254956
        have b1e255019 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e254987
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e254987
          | exact resolve b1e254987 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e254987
        have b1e255188 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have i₁ := b1e1022 (σ x)
             have i₂ := b1e255019
             grind)
          | exact superpose b1e255019 b1e1022
          | exact resolve b1e1022 b1e255019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1022
        have b1e255301 : (M.op (σ y) (σ (M.op y x))) = (k (σ y) (σ (M.op y x))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e16943 (σ y) (σ x)
             have i₂ := b1e255019
             grind)
          | exact superpose b1e255019 b1e16943
          | (have j0 := b1e16943 (M.op (σ y) (σ (M.op y x))) (k (σ y) (σ (M.op y x)))
             grind)
          | exact resolve b1e16943 b1e255019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16943 b1e255019
        have b1e255319 : (σ (k y (M.op y x))) = (M.op (σ y) (σ (M.op y x))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e255301
             have i₂ := b1e16 y (M.op y x)
             grind)
          | exact superpose b1e16 b1e255301
          | exact resolve b1e255301 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e255301
        have b1e255409 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have i₁ := b1e255188
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e255188
          | exact resolve b1e255188 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e255188
        have b1e255419 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op y x))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e255319
             have i₂ := b1e2886
             grind)
          | exact superpose b1e2886 b1e255319
          | exact resolve b1e255319 b1e2886
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2886 b1e255319
        have b1e255469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e255419
             have i₂ := b1e255409
             grind)
          | exact superpose b1e255409 b1e255419
          | exact resolve b1e255419 b1e255409
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e255409 b1e255419
        have b1e255496 : (σ x) = (σ y) := by
          first
          | (have r₁ := b1e255469
             have r₂ := b1e17
             grind)
          | exact resolve b1e255469 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e255469
        have b1e255596 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e12 y
             have i₂ := b1e255496
             grind)
          | exact superpose b1e255496 b1e12
          | exact resolve b1e12 b1e255496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e255496
        have b1e255665 : x = y := by
          first
          | (have i₁ := b1e255596
             have i₂ := b1e12 x
             grind)
          | exact superpose b1e12 b1e255596
          | exact resolve b1e255596 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e255596
        have b1e255695 : False := by grind
        exact b1e255695
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e18 : y = (M.op x x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e22 : x = y := by
          first
          | (have i₁ := b2e18
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e18
          | exact resolve b2e18 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e23 : x = (k x x) := by grind
        have b2e26 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e17
             have i₂ := b2e22
             grind)
          | exact superpose b2e22 b2e17
          | exact resolve b2e17 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e26
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e26
          | exact resolve b2e26 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact superpose b2e15 b2e16
          | (have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e16 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e398 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e41 x x
             grind)
          | exact superpose b2e41 b2e19
          | (have j1 := b2e41 x x
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e41 x y
             grind)
          | exact resolve b2e19 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e447 : (σ y) ≠ (σ (k x x)) := by
          first
          | (have r₁ := b2e398
             have r₂ := b2e27
             grind)
          | exact resolve b2e398 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e398
        have b2e454 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e447
             have i₂ := b2e23
             grind)
          | exact superpose b2e23 b2e447
          | exact resolve b2e447 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e447
        have b2e456 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e454
             have i₂ := b2e22
             grind)
          | exact superpose b2e22 b2e454
          | exact resolve b2e454 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22 b2e454
        have b2e457 : False := by grind
        exact b2e457
      · have b3e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op x x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b3e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e23 : x = (k x y) := by grind
        have b3e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X2 (M.op X0 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e11 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
             have i₂ := b3e11 X0 X2 X1
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e11 (M.op (M.op (M.op X2 X1) X2) X0) X1 X2
             have i₂ := b3e11 X0 X2 (M.op X2 X1)
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e19
             have i₂ := b3e15 (σ x) X0
             grind)
          | (have i₁ := b3e19
             have i₂ := b3e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b3e15 b3e19
          | (have j1 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e15 (σ x) (σ y)
             grind)
          | exact resolve b3e19 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e15 (σ X0) (σ X1)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X0) (σ X1)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e80 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e35 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
             have i₂ := b3e11 X0 X2 X1
             grind)
          | exact superpose b3e11 b3e35
          | exact resolve b3e35 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e132 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b3e45 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e133 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e132
             have i₂ := b3e16 x y
             grind)
          | exact superpose b3e16 b3e132
          | exact resolve b3e132 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132
        have b3e134 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e133
             have i₂ := b3e23
             grind)
          | exact superpose b3e23 b3e133
          | exact resolve b3e133 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e133
        have b3e165 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (M.op X0 X1) (σ x))) (M.op X1 (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 (σ x) X0 X1 (σ y)
             have i₂ := b3e134
             grind)
          | exact superpose b3e134 b3e33
          | exact resolve b3e33 b3e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e134
        have b3e203 : ∀ X1 : G, (σ y) = (M.op (M.op (σ x) X1) (M.op X1 (σ x))) := by
          intro X1
          first
          | (have i₁ := b3e165 x X1
             have i₂ := b3e80 (σ x) x X1 (M.op X1 (σ x))
             grind)
          | exact superpose b3e80 b3e165
          | exact resolve b3e165 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e165
        have b3e524 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e46 x x
             grind)
          | exact superpose b3e46 b3e19
          | (have j1 := b3e46 x x
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e46 x y
             grind)
          | exact resolve b3e19 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e12821 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e524
             have i₂ := b3e15 x x
             grind)
          | exact superpose b3e15 b3e524
          | (have j1 := b3e15 (σ x) (σ x)
             grind)
          | exact resolve b3e524 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e524
        have b3e12824 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b3e12821
             have r₂ := b3e20
             grind)
          | exact resolve b3e12821 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12821
        have b3e12833 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e12824
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e12824
          | exact resolve b3e12824 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12824
        have b3e12834 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b3e12833
        have b3e12852 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e203 (σ x)
             have i₂ := b3e12834
             grind)
          | exact superpose b3e12834 b3e203
          | exact resolve b3e203 b3e12834
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e203 b3e12834
        have b3e12914 : False := by grind
        exact b3e12914
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op x x) := by grind
        have b4e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b4e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e22 : x ≠ y := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e18
          | exact resolve b4e18 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b4e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b4e24
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e24
          | exact resolve b4e24 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e24
        have b4e30 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e25
             grind)
          | exact superpose b4e25 b4e12
          | exact resolve b4e12 b4e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e25
        have b4e31 : x = (k x y) := by
          first
          | (have i₁ := b4e30
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e30
          | exact resolve b4e30 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e30
        have b4e34 : ∀ X0 : G, (M.op x (M.op x (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b4e11 X0 x x
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e54 : x = (M.op x y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b4e31
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e31
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e31 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e31
        have b4e60 : x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b4e54
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e54
          | exact resolve b4e54 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e54
        have b4e63 : x = (M.op x y) := by
          first
          | (have r₁ := b4e60
             have r₂ := b4e22
             grind)
          | exact resolve b4e60 b4e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e60
        have b4e65 : y = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b4e34 y
             have i₂ := b4e63
             grind)
          | exact superpose b4e63 b4e34
          | exact resolve b4e34 b4e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e34 b4e63
        have b4e67 : y = (M.op x x) := by
          first
          | (have i₁ := b4e65
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e65
          | exact resolve b4e65 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e65
        have b4e68 : x = y := by
          first
          | (have i₁ := b4e67
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e67
          | exact resolve b4e67 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e67
        have b4e69 : False := by grind
        exact b4e69
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b5e18 : y ≠ (M.op x x) := by grind
        have b5e19 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b5e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e22 : (σ x) = (k (σ x) (σ y)) := by grind
        have b5e23 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b5e22
             have i₂ := b5e16 x y
             grind)
          | exact superpose b5e16 b5e22
          | exact resolve b5e22 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e22
        have b5e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 X0 X1
             have i₂ := b5e15 (σ X0) (σ X1)
             grind)
          | exact superpose b5e15 b5e16
          | (have j1 := b5e15 (σ X0) (σ X1)
             grind)
          | exact resolve b5e16 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e62 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b5e23
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e23
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e23 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e23
        have b5e63 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b5e62
             have r₂ := b5e18
             grind)
          | exact resolve b5e62 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62
        have b5e529 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e59 x x
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e59
          | exact resolve b5e59 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e59
        have b5e1510 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e12 (k x x)
             have i₂ := b5e529
             grind)
          | exact superpose b5e529 b5e12
          | exact resolve b5e12 b5e529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e529
        have b5e1523 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e1510
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e1510
          | exact resolve b5e1510 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1510
        have b5e1532 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e15 x x
             have i₂ := b5e1523
             grind)
          | exact superpose b5e1523 b5e15
          | (have j0 := b5e15 x y
             grind)
          | exact resolve b5e15 b5e1523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1523
        have b5e1533 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b5e1532
             have r₂ := b5e18
             grind)
          | exact resolve b5e1532 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1532
        have b5e1541 : (σ x) = (σ y) := by
          first
          | (have r₁ := b5e1533
             have r₂ := b5e20
             grind)
          | exact resolve b5e1533 b5e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1533
        have b5e1593 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b5e17
             have i₂ := b5e1541
             grind)
          | exact superpose b5e1541 b5e17
          | exact resolve b5e17 b5e1541
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e1615 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b5e1593
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e1593
          | exact resolve b5e1593 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1593
        have b5e1621 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b5e1615
             have i₂ := b5e1541
             grind)
          | exact superpose b5e1541 b5e1615
          | exact resolve b5e1615 b5e1541
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1541 b5e1615
        have b5e1626 : False := by grind
        exact b5e1626
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : y ≠ (M.op x x) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b6e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e22 : x ≠ y := by
          first
          | (have i₁ := b6e18
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e18
          | exact resolve b6e18 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e15 (σ x) X0
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b6e15 b6e19
          | (have j1 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e19
             have r₂ := b6e15 (σ x) (σ y)
             grind)
          | exact resolve b6e19 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e140 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b6e41 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e141 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e140
             have i₂ := b6e16 x y
             grind)
          | exact superpose b6e16 b6e140
          | exact resolve b6e140 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e140
        have b6e211 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e141
             grind)
          | exact superpose b6e141 b6e17
          | exact resolve b6e17 b6e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e211
             have i₂ := b6e15 x y
             grind)
          | exact superpose b6e15 b6e211
          | (have j1 := b6e15 x y
             grind)
          | exact resolve b6e211 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e211
        have b6e275 : y = (M.op x x) := by grind
        clear b6e274
        have b6e277 : x = y := by
          first
          | (have i₁ := b6e275
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e275
          | exact resolve b6e275 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e275
        have b6e278 : False := by grind
        exact b6e278
      · have b7e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op x x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e46 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b7e19
             have i₂ := b7e15 (σ x) X0
             grind)
          | (have i₁ := b7e19
             have i₂ := b7e15 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b7e15 b7e19
          | (have j1 := b7e15 (σ x) X0
             grind)
          | (have r₁ := b7e19
             have r₂ := b7e15 (σ x) (σ y)
             grind)
          | exact resolve b7e19 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e125 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b7e46 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46
        have b7e126 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e125
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e125
          | exact resolve b7e125 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e125
        have b7e182 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e126
             grind)
          | exact superpose b7e126 b7e17
          | exact resolve b7e17 b7e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e126
        have b7e240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b7e182
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e182
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e182 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e182
        have b7e241 : y = (M.op x x) := by grind
        clear b7e240
        have b7e243 : False := by grind
        exact b7e243

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation947 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x x) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
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
      have b0e31 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 x))) := by
        intro X0
        first
        | (have i₁ := b0e10 x X0 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ y) (M.op X0 (σ x)))) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) X0 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
           have i₂ := b0e10 X0 X2 X3
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) y)) := by
        intro X0
        first
        | (have i₁ := b0e10 x x X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
           have i₂ := b0e10 X0 X1 X3
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b0e31 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e31
        | exact resolve b0e31 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e45 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X1 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X2 X1 X1
           have i₂ := b0e14 (M.op X1 X2) X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op (M.op X2 X0) (M.op X1 X0))
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 (M.op X1 X2) X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op X0 (M.op y y)))) := by
        intro X0
        first
        | (have i₁ := b0e10 (M.op y y) X0 x
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e24 X1 X0
           have i₂ := b0e14 X0 (τ X1)
           grind)
        | exact superpose b0e14 b0e24
        | (have j1 := b0e14 X0 (τ X1)
           grind)
        | exact resolve b0e24 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e63 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24
      have b0e86 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e44 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e114 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      have b0e128 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e114 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e114
        | exact resolve b0e114 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114
      have b0e148 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b0e86 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e86
        | (have j0 := b0e86 x x
           grind)
        | exact resolve b0e86 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e222 : ∀ X0 X1 : G, (M.op (σ x) X1) = (k (σ x) X1) ∨ (M.op X0 X1) = (M.op (σ y) (M.op X0 (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e47 X0 X0 (M.op (σ y) (M.op X0 (σ x)))
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e47
        | (have j0 := b0e47 X1 (σ x) (k (σ x) X1)
           grind)
        | exact resolve b0e47 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e47
      have b0e324 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1
           have i₂ := b0e49 X0 X1
           grind)
        | exact superpose b0e49 b0e11
        | (have j1 := b0e49 X0 X1
           grind)
        | exact resolve b0e11 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e344 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e49 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e422 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 X0 X2 X2 X1
           have i₂ := b0e10 X0 X2 X1
           grind)
        | exact superpose b0e10 b0e33
        | exact resolve b0e33 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e506 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
           have i₂ := b0e36 X1 (M.op X2 X1) X3 X0
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e513 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e506 X1 x X2 X3
           have i₂ := b0e422 x X1 (M.op X2 x)
           grind)
        | exact superpose b0e422 b0e506
        | exact resolve b0e506 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e506
      have b0e535 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
        intro X1 X3
        first
        | (have i₁ := b0e513 x X1 X3
           have i₂ := b0e422 x X1 x
           grind)
        | exact superpose b0e422 b0e513
        | exact resolve b0e513 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e513
      have b0e614 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0)))) = (M.op X3 (M.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op (M.op X2 X0) (M.op X1 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e422 (M.op (M.op X2 X0) (M.op X1 X0)) X1 X3
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e422
        | exact resolve b0e422 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e616 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op y (M.op X0 x)))) = (M.op X1 (M.op (M.op y (M.op X0 x)) (M.op y (M.op X0 x)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e422 (M.op y (M.op X0 x)) X0 X1
           have i₂ := b0e31 X0
           grind)
        | exact superpose b0e31 b0e422
        | exact resolve b0e422 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e627 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e422 x x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e422
        | exact resolve b0e422 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e640 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e422 (σ x) x (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e422
        | exact resolve b0e422 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e653 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 X0 x
           have i₂ := b0e422 X1 x X0
           grind)
        | exact superpose b0e422 b0e10
        | exact resolve b0e10 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e698 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op y (M.op X0 x)))) = (M.op X1 (M.op y (M.op (M.op X0 x) (M.op X0 x)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e616 X0 X1
           have i₂ := b0e422 (M.op X0 x) y y
           grind)
        | exact superpose b0e422 b0e616
        | exact resolve b0e616 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e616
      have b0e700 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0)))) = (M.op X3 (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e614 X0 X1 X2 X3
           have i₂ := b0e422 (M.op X1 X0) (M.op X2 X0) (M.op X2 X0)
           grind)
        | exact superpose b0e422 b0e614
        | exact resolve b0e614 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e614
      have b0e719 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op y (M.op X0 x)))) = (M.op X1 (M.op y (M.op X0 (M.op x x)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e698 X0 X1
           have i₂ := b0e422 x X0 X0
           grind)
        | exact superpose b0e422 b0e698
        | exact resolve b0e698 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e698
      have b0e721 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0)))) = (M.op X3 (M.op (M.op X2 X0) (M.op X1 (M.op X0 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e700 X0 X1 X2 X3
           have i₂ := b0e422 X0 X1 X1
           grind)
        | exact superpose b0e422 b0e700
        | exact resolve b0e700 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e700
      have b0e728 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op y (M.op X0 x)))) = (M.op X1 (M.op y (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e719 X0 X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e719
        | exact resolve b0e719 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e719
      have b0e730 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X2 X0) (M.op X1 (M.op X0 X0)))) = (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e721 X0 X1 X2 X3
           have i₂ := b0e422 X0 X2 X1
           grind)
        | exact superpose b0e422 b0e721
        | exact resolve b0e721 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e721
      have b0e735 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op X0 y))) = (M.op x (M.op X1 (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e728 X0 X1
           have i₂ := b0e627 X0
           grind)
        | exact superpose b0e627 b0e728
        | exact resolve b0e728 b0e627
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e728
      have b0e742 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e627 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e627
        | exact resolve b0e627 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e745 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e31 X0
           have i₂ := b0e627 X0
           grind)
        | exact superpose b0e627 b0e31
        | exact resolve b0e31 b0e627
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e759 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 x) (M.op X0 x))) = (M.op (M.op X1 (M.op X0 x)) (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e422 (M.op X0 x) X1 y
           have i₂ := b0e627 X0
           grind)
        | exact superpose b0e627 b0e422
        | exact resolve b0e422 b0e627
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e627
      have b0e762 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op x x))) = (M.op (M.op X1 (M.op X0 x)) (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e759 X0 X1
           have i₂ := b0e422 x X0 X0
           grind)
        | exact superpose b0e422 b0e759
        | exact resolve b0e759 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e759
      have b0e767 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op X1 (M.op X0 x)) (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e762 X0 X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e762
        | exact resolve b0e762 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e762
      have b0e827 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b0e10 y y X0
           have i₂ := b0e742
           grind)
        | exact superpose b0e742 b0e10
        | exact resolve b0e10 b0e742
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e841 : y = (M.op y (M.op x (M.op y y))) := by
        first
        | (have i₁ := b0e827 x
           have i₂ := b0e422 y x x
           grind)
        | exact superpose b0e422 b0e827
        | exact resolve b0e827 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e827
      have b0e844 : y = (M.op y x) := by
        first
        | (have i₁ := b0e841
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e841
        | exact resolve b0e841 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e841
      have b0e888 : y ≠ y ∨ y = (k y x) := by
        first
        | (have i₁ := b0e86 y x
           have i₂ := b0e844
           grind)
        | exact superpose b0e844 b0e86
        | (have j0 := b0e86 y x
           grind)
        | (have r₁ := b0e86 y x
           have r₂ := b0e844
           grind)
        | exact resolve b0e86 b0e844
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86 b0e844
      have b0e891 : y = (k y x) := by grind
      clear b0e888
      have b0e1437 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e653 X0 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e653
        | exact resolve b0e653 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1442 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b0e653 X0 y
           have i₂ := b0e742
           grind)
        | exact superpose b0e742 b0e653
        | exact resolve b0e653 b0e742
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1448 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e653 (M.op X1 X0) X0
           have i₂ := b0e422 X0 X1 X0
           grind)
        | exact superpose b0e422 b0e653
        | exact resolve b0e653 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1456 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 X1 X1 X0 X0
           have i₂ := b0e653 X1 (M.op X0 X1)
           grind)
        | exact superpose b0e653 b0e33
        | exact resolve b0e33 b0e653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e1469 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e422 (M.op X1 (M.op X0 X0)) X1 X2
           have i₂ := b0e653 X1 X0
           grind)
        | exact superpose b0e653 b0e422
        | exact resolve b0e422 b0e653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1478 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1469 X0 X1 X2
           have i₂ := b0e422 (M.op X0 X0) X1 X1
           grind)
        | exact superpose b0e422 b0e1469
        | exact resolve b0e1469 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1469
      have b0e1481 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op X0 (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1456 X0 X1
           have i₂ := b0e422 X1 X0 X0
           grind)
        | exact superpose b0e422 b0e1456
        | exact resolve b0e1456 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1456
      have b0e1484 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op X0 X0)))) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1478 X0 X1 X2
           have i₂ := b0e422 X0 X0 X0
           grind)
        | exact superpose b0e422 b0e1478
        | exact resolve b0e1478 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1478
      have b0e1492 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X2 X0)) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e535 X0 x
           have i₂ := b0e14 X0 X1
           grind)
        | (have i₁ := b0e535 X1 x
           have i₂ := b0e14 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e14 b0e535
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e535 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1500 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e535 (M.op X1 X1) x
           have i₂ := b0e653 (M.op X1 X1) X1
           grind)
        | exact superpose b0e653 b0e535
        | exact resolve b0e535 b0e653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e535 b0e653
      have b0e1526 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op X2 X0)) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e1492 X0 x X2
           have i₂ := b0e1500 (M.op X2 X0) x
           grind)
        | exact superpose b0e1500 b0e1492
        | (have j0 := b0e1492 X0 x X2
           grind)
        | exact resolve b0e1492 b0e1500
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1492
      have b0e1540 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e1526 X0 X2
           have i₂ := b0e422 X0 X2 X2
           grind)
        | exact superpose b0e422 b0e1526
        | (have j0 := b0e1526 X0 X2
           grind)
        | exact resolve b0e1526 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1526
      have b0e1660 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 X1
           have i₂ := b0e58 X0 X1
           grind)
        | exact superpose b0e58 b0e12
        | (have j1 := b0e58 X0 X1
           grind)
        | exact resolve b0e12 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e1719 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) = (M.op X1 (M.op (M.op X1 (σ y)) (M.op X1 (σ y)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e422 (M.op X1 (σ y)) X0 X1
           have i₂ := b0e1437 X1
           grind)
        | exact superpose b0e1437 b0e422
        | exact resolve b0e422 b0e1437
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1724 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ y) (M.op X0 (σ y)) X0
           have i₂ := b0e1437 (M.op X0 (σ y))
           grind)
        | exact superpose b0e1437 b0e10
        | exact resolve b0e10 b0e1437
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1730 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1719 X0 X1
           have i₂ := b0e10 (σ y) X1 X1
           grind)
        | exact superpose b0e10 b0e1719
        | exact resolve b0e1719 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1719
      have b0e2125 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op (M.op X0 y) (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e1500 (M.op X0 y) X0
           have i₂ := b0e745 X0
           grind)
        | exact superpose b0e745 b0e1500
        | exact resolve b0e1500 b0e745
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2235 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op x (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e2125 X0
           have i₂ := b0e422 y X0 X0
           grind)
        | exact superpose b0e422 b0e2125
        | exact resolve b0e2125 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2125
      have b0e2264 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e2235 X0
           have i₂ := b0e742
           grind)
        | exact superpose b0e742 b0e2235
        | exact resolve b0e2235 b0e742
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2235
      have b0e4697 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X1 (σ y)) (M.op (M.op X2 (M.op (M.op X0 (σ x)) (σ y))) (σ x))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e36 (σ x) (M.op X0 (σ y)) X2 x
           have i₂ := b0e1724 X0
           grind)
        | exact superpose b0e1724 b0e36
        | exact resolve b0e36 b0e1724
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e1724
      have b0e4713 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e4697 X0 X1 x
           have i₂ := b0e1730 x (M.op X0 (σ x))
           grind)
        | exact superpose b0e1730 b0e4697
        | exact resolve b0e4697 b0e1730
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1730 b0e4697
      have b0e4718 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e4713 X0 x
           have i₂ := b0e1500 (σ y) x
           grind)
        | exact superpose b0e1500 b0e4713
        | exact resolve b0e4713 b0e1500
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1500 b0e4713
      have b0e4722 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e4718 x
           have i₂ := b0e640 x
           grind)
        | exact superpose b0e640 b0e4718
        | exact resolve b0e4718 b0e640
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e640 b0e4718
      have b0e4769 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) := by
        first
        | (have i₁ := b0e324 x x
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e324
        | exact resolve b0e324 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e324
      have b0e4813 : (σ y) = (σ (k x x)) ∨ x = y := by
        first
        | (have i₁ := b0e4769
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e4769
        | exact resolve b0e4769 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4769
      have b0e4837 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e15 (k x x) X0
           have i₂ := b0e4813
           grind)
        | exact superpose b0e4813 b0e15
        | exact resolve b0e15 b0e4813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4851 : ∀ X0 : G, (k (k x x) (τ X0)) = (τ (k (σ y) X0)) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e63 (k x x) X0
           have i₂ := b0e4813
           grind)
        | exact superpose b0e4813 b0e63
        | exact resolve b0e63 b0e4813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4813
      have b0e4862 : ∀ X0 : G, (k y (τ X0)) = (k (k x x) (τ X0)) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e4851 X0
           have i₂ := b0e63 y X0
           grind)
        | exact superpose b0e63 b0e4851
        | exact resolve b0e4851 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63 b0e4851
      have b0e4875 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e4837 X0
           have i₂ := b0e15 y X0
           grind)
        | exact superpose b0e15 b0e4837
        | exact resolve b0e4837 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4837
      have b0e5651 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op (M.op X0 y) (M.op (M.op X0 y) (M.op X0 y)))) := by
        intro X0
        first
        | (have i₁ := b0e1448 (M.op X0 y) X0
           have i₂ := b0e745 X0
           grind)
        | exact superpose b0e745 b0e1448
        | exact resolve b0e1448 b0e745
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e5653 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e1448 X0 X0
           have i₂ := b0e14 X0 X1
           grind)
        | (have i₁ := b0e1448 X0 X1
           have i₂ := b0e14 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e14 b0e1448
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e1448 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1448
      have b0e5806 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op (M.op X0 y) (M.op X0 (M.op y y)))) := by
        intro X0
        first
        | (have i₁ := b0e5651 X0
           have i₂ := b0e422 y X0 X0
           grind)
        | exact superpose b0e422 b0e5651
        | exact resolve b0e5651 b0e422
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5651
      have b0e5840 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op x (M.op X0 (M.op y y)))) := by
        intro X0
        first
        | (have i₁ := b0e5806 X0
           have i₂ := b0e730 y X0 X0 x
           grind)
        | exact superpose b0e730 b0e5806
        | exact resolve b0e5806 b0e730
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e730 b0e5806
      have b0e5868 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 (M.op y (M.op y y)))) := by
        intro X0
        first
        | (have i₁ := b0e5840 X0
           have i₂ := b0e1484 y X0 x
           grind)
        | (have i₁ := b0e5840 y
           have i₂ := b0e1484 y x y
           grind)
        | exact superpose b0e1484 b0e5840
        | exact resolve b0e5840 b0e1484
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1484 b0e5840
      have b0e5885 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e5868 X0
           have i₂ := b0e745 y
           grind)
        | exact superpose b0e745 b0e5868
        | exact resolve b0e5868 b0e745
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e745 b0e5868
      have b0e6614 : ∀ X0 X1 : G, (M.op X0 x) = (M.op x (M.op (M.op X1 (M.op X0 x)) (M.op X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 (M.op X0 x) x X1
           have i₂ := b0e5885 X0
           grind)
        | exact superpose b0e5885 b0e10
        | exact resolve b0e10 b0e5885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5885
      have b0e6640 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op y (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e6614 X0 x
           have i₂ := b0e767 X0 x
           grind)
        | exact superpose b0e767 b0e6614
        | exact resolve b0e6614 b0e767
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e767 b0e6614
      have b0e6661 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op x (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e6640 X0
           have i₂ := b0e735 X0 x
           grind)
        | exact superpose b0e735 b0e6640
        | exact resolve b0e6640 b0e735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6640
      have b0e6997 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b0e222 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e222
        | exact resolve b0e222 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e222
      have b0e7328 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b0e6997
           have i₂ := b0e4722
           grind)
        | exact superpose b0e4722 b0e6997
        | exact resolve b0e6997 b0e4722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6997
      have b0e7421 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x x)) := by
        first
        | (have i₁ := b0e7328
           have i₂ := b0e15 x x
           grind)
        | exact superpose b0e15 b0e7328
        | exact resolve b0e7328 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7328
      have b0e9966 : ∀ X0 : G, y = (M.op X0 (M.op x (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e1442 X0
           have i₂ := b0e2264 X0
           grind)
        | (have i₁ := b0e1442 x
           have i₂ := b0e2264 x
           grind)
        | exact superpose b0e2264 b0e1442
        | exact resolve b0e1442 b0e2264
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1442
      have b0e12811 : y = (k y (τ (M.op (σ x) (σ y)))) := by
        first
        | (have i₁ := b0e128 y
           have i₂ := b0e4722
           grind)
        | exact superpose b0e4722 b0e128
        | exact resolve b0e128 b0e4722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128
      have b0e12819 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
      have b0e40884 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op y (M.op X0 y)))) := by
        intro X0
        first
        | (have i₁ := b0e53 X0
           have i₂ := b0e1481 X0 y
           grind)
        | (have i₁ := b0e53 y
           have i₂ := b0e1481 y y
           grind)
        | exact superpose b0e1481 b0e53
        | exact resolve b0e53 b0e1481
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53 b0e1481
      have b0e41078 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op x (M.op X0 y)))) := by
        intro X0
        first
        | (have i₁ := b0e40884 X0
           have i₂ := b0e735 X0 x
           grind)
        | exact superpose b0e735 b0e40884
        | exact resolve b0e40884 b0e735
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e735 b0e40884
      have b0e41116 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e41078 X0
           have i₂ := b0e6661 X0
           grind)
        | exact superpose b0e6661 b0e41078
        | exact resolve b0e41078 b0e6661
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6661 b0e41078
      have b0e41152 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e41116 X0
           have i₂ := b0e742
           grind)
        | exact superpose b0e742 b0e41116
        | exact resolve b0e41116 b0e742
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41116
      have b0e42614 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 x)) (M.op x y)) = (M.op X1 (M.op (M.op X1 x) (M.op X1 x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e422 (M.op X1 x) X0 X1
           have i₂ := b0e41152 X1
           grind)
        | exact superpose b0e41152 b0e422
        | exact resolve b0e422 b0e41152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e422
      have b0e42671 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 x)) (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e42614 X0 X1
           have i₂ := b0e10 x X1 X1
           grind)
        | exact superpose b0e10 b0e42614
        | exact resolve b0e42614 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42614
      have b0e42712 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 (M.op X1 x)) y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e42671 X0 X1
           have i₂ := b0e2264 (M.op X0 (M.op X1 x))
           grind)
        | exact superpose b0e2264 b0e42671
        | exact resolve b0e42671 b0e2264
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42671
      have b0e45886 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 x)) x) := by
        intro X0 X1
        first
        | (have i₁ := b0e9966 (M.op X0 (M.op X1 x))
           have i₂ := b0e42712 X0 X1
           grind)
        | exact superpose b0e42712 b0e9966
        | exact resolve b0e9966 b0e42712
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9966 b0e42712
      have b0e46585 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e45886 X0 (M.op x X0)
           have i₂ := b0e45 x X0 x
           grind)
        | exact superpose b0e45 b0e45886
        | (have j1 := b0e45 x X0 x
           grind)
        | exact resolve b0e45886 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e45886
      have b0e109245 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b0e1437 (σ y)
           have i₂ := b0e1540 (σ y) (σ y)
           grind)
        | exact superpose b0e1540 b0e1437
        | (have j1 := b0e1540 (σ y) (σ y)
           grind)
        | exact resolve b0e1437 b0e1540
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1437 b0e1540
      have b0e109371 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e109245
           have i₂ := b0e15 y y
           grind)
        | exact superpose b0e15 b0e109245
        | exact resolve b0e109245 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109245
      have b0e109404 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e109371
           have i₂ := b0e4722
           grind)
        | exact superpose b0e4722 b0e109371
        | exact resolve b0e109371 b0e4722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109371
      have b0e116212 : y = (k y (τ (σ y))) ∨ (σ y) = (σ (k x x)) := by
        first
        | (have i₁ := b0e12811
           have i₂ := b0e7421
           grind)
        | exact superpose b0e7421 b0e12811
        | exact resolve b0e12811 b0e7421
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7421 b0e12811
      have b0e116247 : (σ y) = (σ (k x x)) ∨ y = (k y y) := by
        first
        | (have i₁ := b0e116212
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e116212
        | exact resolve b0e116212 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116212
      have b0e116280 : (k x x) = (τ (σ y)) ∨ y = (k y y) := by
        first
        | (have i₁ := b0e11 (k x x)
           have i₂ := b0e116247
           grind)
        | exact superpose b0e116247 b0e11
        | exact resolve b0e11 b0e116247
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116247
      have b0e116294 : y = (k y y) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e116280
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e116280
        | exact resolve b0e116280 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116280
      have b0e116332 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e344 y
           have i₂ := b0e116294
           grind)
        | exact superpose b0e116294 b0e344
        | (have j0 := b0e344 y
           grind)
        | exact resolve b0e344 b0e116294
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e344 b0e116294
      have b0e116347 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by grind
      clear b0e116332
      have b0e116361 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e116347
           have i₂ := b0e4722
           grind)
        | exact superpose b0e4722 b0e116347
        | exact resolve b0e116347 b0e4722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4722 b0e116347
      have b0e116563 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e116361
           grind)
        | exact superpose b0e116361 b0e16
        | exact resolve b0e16 b0e116361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e116568 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e12819
           have i₂ := b0e116361
           grind)
        | exact superpose b0e116361 b0e12819
        | exact resolve b0e12819 b0e116361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12819 b0e116361
      have b0e116629 : (σ y) = (σ (k y y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e116568
           have i₂ := b0e15 y y
           grind)
        | exact superpose b0e15 b0e116568
        | exact resolve b0e116568 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116568
      have b0e117399 : ∀ X0 : G, (k y X0) = (k (k x x) X0) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b0e4862 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e4862
        | exact resolve b0e4862 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4862
      have b0e117481 : (k y x) = (M.op (k x x) x) ∨ y = (M.op (k x x) x) ∨ x = y := by
        first
        | (have i₁ := b0e46585 (k x x)
           have i₂ := b0e117399 x
           grind)
        | exact superpose b0e117399 b0e46585
        | (have j0 := b0e46585 (k x x)
           grind)
        | exact resolve b0e46585 b0e117399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46585 b0e117399
      have b0e117494 : y = (M.op (k x x) x) ∨ y = (M.op (k x x) x) ∨ x = y := by
        first
        | (have i₁ := b0e117481
           have i₂ := b0e891
           grind)
        | exact superpose b0e891 b0e117481
        | exact resolve b0e117481 b0e891
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e891 b0e117481
      have b0e117495 : y = (M.op (k x x) x) ∨ x = y := by grind
      clear b0e117494
      have b0e118933 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have j0 := b0e1660 (τ X0) X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1660
      have b0e118934 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e118933 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e118933
        | (have j0 := b0e118933 X0
           grind)
        | exact resolve b0e118933 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118933
      have b0e119270 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b0e118934 (σ X0)
           have i₂ := b0e15 X0 X0
           grind)
        | exact superpose b0e15 b0e118934
        | (have j0 := b0e118934 (σ X0)
           grind)
        | exact resolve b0e118934 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118934
      have b0e119300 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e119270 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e119270
        | (have j0 := b0e119270 X0
           grind)
        | exact resolve b0e119270 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e119270
      have b0e125326 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 ∨ (M.op x y) = (k X0 (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e5653 (M.op X0 x) X0
           have i₂ := b0e41152 X0
           grind)
        | exact superpose b0e41152 b0e5653
        | exact resolve b0e5653 b0e41152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5653 b0e41152
      have b0e125537 : ∀ X0 : G, (M.op x (M.op (M.op X0 x) y)) = X0 ∨ (M.op x y) = (k X0 (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e125326 X0
           have i₂ := b0e2264 (M.op X0 x)
           grind)
        | exact superpose b0e2264 b0e125326
        | (have j0 := b0e125326 X0
           grind)
        | exact resolve b0e125326 b0e2264
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2264 b0e125326
      have b0e125549 : ∀ X0 : G, (M.op x y) = (k X0 (M.op X0 x)) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b0e125537 X0
           have i₂ := b0e34 X0
           grind)
        | exact superpose b0e34 b0e125537
        | (have j0 := b0e125537 X0
           grind)
        | exact resolve b0e125537 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e125537
      have b0e125573 : (M.op x y) = (k (k x x) y) ∨ x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b0e125549 (k x x)
           have i₂ := b0e117495
           grind)
        | exact superpose b0e117495 b0e125549
        | (have j0 := b0e125549 (k x x)
           grind)
        | exact resolve b0e125549 b0e117495
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117495 b0e125549
      have b0e125602 : (M.op x y) = (k (k x x) y) ∨ x = (k x x) := by
        first
        | (have r₁ := b0e125573
           have r₂ := b0e148
           grind)
        | exact resolve b0e125573 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125573
      have b0e130794 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e119300 y
           have i₂ := b0e116629
           grind)
        | exact superpose b0e116629 b0e119300
        | (have j0 := b0e119300 y
           grind)
        | (have r₁ := b0e119300 y
           have r₂ := b0e116629
           grind)
        | exact resolve b0e119300 b0e116629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116629 b0e119300
      have b0e130796 : (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by grind
      clear b0e130794
      have b0e130802 : (σ (M.op x y)) = (σ y) ∨ y = (k x x) := by
        first
        | (have i₁ := b0e130796
           have i₂ := b0e742
           grind)
        | exact superpose b0e742 b0e130796
        | exact resolve b0e130796 b0e742
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e742 b0e130796
      have b0e130820 : y = (k x x) := by
        first
        | (have r₁ := b0e130802
           have r₂ := b0e116563
           grind)
        | exact resolve b0e130802 b0e116563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116563 b0e130802
      have b0e155460 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (k x x) := by
        first
        | (have i₁ := b0e4875 y
           have i₂ := b0e125602
           grind)
        | exact superpose b0e125602 b0e4875
        | exact resolve b0e4875 b0e125602
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4875 b0e125602
      have b0e155471 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (k x x) := by
        first
        | (have r₁ := b0e155460
           have r₂ := b0e148
           grind)
        | exact resolve b0e155460 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148 b0e155460
      have b0e155475 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b0e155471
           have i₂ := b0e130820
           grind)
        | exact superpose b0e130820 b0e155471
        | exact resolve b0e155471 b0e130820
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130820 b0e155471
      have b0e164030 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e109404
           grind)
        | exact superpose b0e109404 b0e16
        | exact resolve b0e16 b0e109404
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109404
      have b0e164060 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e164030
           have i₂ := b0e155475
           grind)
        | exact superpose b0e155475 b0e164030
        | (have r₁ := b0e164030
           have r₂ := b0e155475
           grind)
        | exact resolve b0e164030 b0e155475
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155475 b0e164030
      have b0e164063 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e164060
      have b0e164122 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e11 y
           have i₂ := b0e164063
           grind)
        | exact superpose b0e164063 b0e11
        | exact resolve b0e11 b0e164063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164063
      have b0e164177 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e164122
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e164122
        | exact resolve b0e164122 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164122
      have b0e164178 : x = y := by grind
      clear b0e164177
      have b0e164196 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e164178
           grind)
        | exact superpose b0e164178 b0e16
        | exact resolve b0e16 b0e164178
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164178
      have b0e164708 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e164196
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e164196
        | exact resolve b0e164196 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164196
      have b0e164782 : False := by grind
      exact b0e164782
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : y = (M.op x x) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : x = (k x y) := by grind
      have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
           have i₂ := b1e10 X0 X2 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
           have i₂ := b1e10 X0 X1 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e39 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e43 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b1e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b1e80 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e43 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e43
      have b1e81 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e80
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e80
        | exact resolve b1e80 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e80
      have b1e82 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e81
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e81
        | exact resolve b1e81 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e81
      have b1e83 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e82
           grind)
        | exact superpose b1e82 b1e16
        | exact resolve b1e16 b1e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e251 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 X1
           have i₂ := b1e44 X0 X1
           grind)
        | exact superpose b1e44 b1e11
        | (have j1 := b1e44 X0 X1
           grind)
        | exact resolve b1e11 b1e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e44
      have b1e319 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e30 X0 X2 X2 X1
           have i₂ := b1e10 X0 X2 X1
           grind)
        | exact superpose b1e10 b1e30
        | exact resolve b1e30 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30
      have b1e383 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
           have i₂ := b1e32 X1 (M.op X2 X1) X3 X0
           grind)
        | exact superpose b1e32 b1e10
        | exact resolve b1e10 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32
      have b1e388 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
        intro X1 X2 X3
        first
        | (have i₁ := b1e383 X1 x X2 X3
           have i₂ := b1e319 x X1 (M.op X2 x)
           grind)
        | exact superpose b1e319 b1e383
        | exact resolve b1e383 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e383
      have b1e409 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
        intro X1 X3
        first
        | (have i₁ := b1e388 x X1 X3
           have i₂ := b1e319 x X1 x
           grind)
        | exact superpose b1e319 b1e388
        | exact resolve b1e388 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e388
      have b1e514 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b1e319 x x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e319
        | exact resolve b1e319 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e537 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 X0 x
           have i₂ := b1e319 X1 x X0
           grind)
        | exact superpose b1e319 b1e10
        | exact resolve b1e10 b1e319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e319
      have b1e612 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b1e514 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e514
        | exact resolve b1e514 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e514
      have b1e1351 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e409 (M.op X1 X1) x
           have i₂ := b1e537 (M.op X1 X1) X1
           grind)
        | exact superpose b1e537 b1e409
        | exact resolve b1e409 b1e537
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e409 b1e537
      have b1e1609 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e1351 (σ y) (σ x)
           have i₂ := b1e82
           grind)
        | exact superpose b1e82 b1e1351
        | exact resolve b1e1351 b1e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1351
      have b1e1681 : (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e1609
           have i₂ := b1e82
           grind)
        | exact superpose b1e82 b1e1609
        | exact resolve b1e1609 b1e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e82 b1e1609
      have b1e4220 : (σ x) = (σ (k y y)) ∨ y = (τ (σ x)) := by
        first
        | (have i₁ := b1e251 y y
           have i₂ := b1e1681
           grind)
        | exact superpose b1e1681 b1e251
        | exact resolve b1e251 b1e1681
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e251 b1e1681
      have b1e4260 : (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b1e4220
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e4220
        | exact resolve b1e4220 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4220
      have b1e4580 : (σ x) = (σ (M.op y y)) ∨ x = y ∨ y = (k y y) := by
        first
        | (have i₁ := b1e4260
           have i₂ := b1e39 y y
           grind)
        | exact superpose b1e39 b1e4260
        | (have j1 := b1e39 y y
           grind)
        | exact resolve b1e4260 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39
      have b1e4584 : (k y y) = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e11 (k y y)
           have i₂ := b1e4260
           grind)
        | exact superpose b1e4260 b1e11
        | exact resolve b1e11 b1e4260
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4260
      have b1e4619 : x = (k y y) ∨ x = y := by
        first
        | (have i₁ := b1e4584
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e4584
        | exact resolve b1e4584 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4584
      have b1e4623 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (k y y) := by
        first
        | (have i₁ := b1e4580
           have i₂ := b1e612
           grind)
        | exact superpose b1e612 b1e4580
        | exact resolve b1e4580 b1e612
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e612 b1e4580
      have b1e4630 : y = (k y y) ∨ x = y := by
        first
        | (have r₁ := b1e4623
           have r₂ := b1e83
           grind)
        | exact resolve b1e4623 b1e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4623
      have b1e5329 : x = y ∨ x = y ∨ x = y := by
        first
        | (have i₁ := b1e4619
           have i₂ := b1e4630
           grind)
        | exact superpose b1e4630 b1e4619
        | exact resolve b1e4619 b1e4630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4619 b1e4630
      have b1e5344 : x = y := by grind
      clear b1e5329
      have b1e5555 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e83
           have i₂ := b1e5344
           grind)
        | exact superpose b1e5344 b1e83
        | exact resolve b1e83 b1e5344
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83
      have b1e5594 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e5555
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e5555
        | exact resolve b1e5555 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5555
      have b1e5605 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e5594
           have i₂ := b1e5344
           grind)
        | exact superpose b1e5344 b1e5594
        | exact resolve b1e5594 b1e5344
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5344 b1e5594
      have b1e5606 : False := by grind
      exact b1e5606
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b2e44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e51 : x = (M.op x y) ∨ y = (M.op x x) := by
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
      have b2e54 : x = (M.op x y) := by
        first
        | (have r₁ := b2e51
           have r₂ := b2e17
           grind)
        | exact resolve b2e51 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e311 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e49 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e49
        | exact resolve b2e49 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e595 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e311
           grind)
        | exact superpose b2e311 b2e11
        | exact resolve b2e11 b2e311
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e311
      have b2e608 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e595
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e595
        | exact resolve b2e595 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e595
      have b2e615 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e44 x x
           have i₂ := b2e608
           grind)
        | exact superpose b2e608 b2e44
        | exact resolve b2e44 b2e608
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44 b2e608
      have b2e618 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e615
           have r₂ := b2e17
           grind)
        | exact resolve b2e615 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e615
      have b2e759 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e618
           grind)
        | exact superpose b2e618 b2e11
        | exact resolve b2e11 b2e618
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e618
      have b2e775 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e759
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e759
        | exact resolve b2e759 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e759
      have b2e776 : x = y := by grind
      clear b2e775
      have b2e832 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e776
           grind)
        | exact superpose b2e776 b2e16
        | exact resolve b2e16 b2e776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e838 : x = (M.op x x) := by
        first
        | (have i₁ := b2e54
           have i₂ := b2e776
           grind)
        | exact superpose b2e776 b2e54
        | exact resolve b2e54 b2e776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54
      have b2e844 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e832
           have i₂ := b2e838
           grind)
        | exact superpose b2e838 b2e832
        | exact resolve b2e832 b2e838
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e832 b2e838
      have b2e846 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e844
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e844
        | exact resolve b2e844 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e844
      have b2e847 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e846
           have i₂ := b2e776
           grind)
        | exact superpose b2e776 b2e846
        | exact resolve b2e846 b2e776
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e776 b2e846
      have b2e848 : False := by grind
      exact b2e848
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e36 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e66 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e36 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e67 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e66
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e66
        | exact resolve b3e66 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e66
      have b3e145 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e67
           grind)
        | exact superpose b3e67 b3e16
        | exact resolve b3e16 b3e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e67
      have b3e178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e145
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e145
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e145 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e145
      have b3e179 : y = (M.op x x) := by grind
      clear b3e178
      have b3e183 : False := by grind
      exact b3e183

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation960 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op x x) := by grind
      have b0e18 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e10 X0 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
           have i₂ := b0e10 X0 X2 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 x X0 X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 (σ x) X0 X1
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
           have i₂ := b0e10 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : (σ x) = (M.op x (M.op y (σ y))) := by
        first
        | (have i₁ := b0e31 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e31
        | exact resolve b0e31 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e31 (M.op y y)
           have i₂ := b0e10 y y y
           grind)
        | exact superpose b0e10 b0e31
        | exact resolve b0e31 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 (M.op y (M.op X0 X0)) x
           have i₂ := b0e31 X0
           grind)
        | exact superpose b0e31 b0e10
        | exact resolve b0e10 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 (σ X0) (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 y X0 X1
           have i₂ := b0e39
           grind)
        | exact superpose b0e39 b0e10
        | exact resolve b0e10 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : y = (k y (M.op x y)) := by grind
      clear b0e39
      have b0e60 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) y) (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 (M.op (M.op X0 X1) y) X1
           have i₂ := b0e34 X1 X0
           grind)
        | exact superpose b0e34 b0e34
        | exact resolve b0e34 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e83 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
        first
        | (have i₁ := b0e32 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e32
        | exact resolve b0e32 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e86 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e32 (M.op (σ y) (σ y))
           have i₂ := b0e10 (σ y) (σ y) (σ y)
           grind)
        | exact superpose b0e10 b0e32
        | exact resolve b0e32 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e89 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b0e83
           have i₂ := b0e86
           grind)
        | exact superpose b0e86 b0e83
        | exact resolve b0e83 b0e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e141 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x (M.op y (M.op X0 (M.op X1 X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 (M.op X1 X0)
           have i₂ := b0e36 X1 X0
           grind)
        | exact superpose b0e36 b0e31
        | exact resolve b0e31 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e142 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X1 X0) X2 X3
           have i₂ := b0e36 X1 X0
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e216 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
           have i₂ := b0e33 X1 x x X0
           grind)
        | exact superpose b0e33 b0e34
        | exact resolve b0e34 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e217 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e10 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
           have i₂ := b0e33 X1 x x X0
           grind)
        | exact superpose b0e33 b0e10
        | exact resolve b0e10 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e487 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 X2))) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X2 (σ X1) (σ X0)
           have i₂ := b0e52 X0 X1
           grind)
        | exact superpose b0e52 b0e10
        | (have j1 := b0e52 X0 X1
           grind)
        | exact resolve b0e10 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e504 : ∀ X0 X1 : G, (σ X1) = (M.op x (M.op y (σ X0))) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 (σ X1)
           have i₂ := b0e52 X1 X0
           grind)
        | exact superpose b0e52 b0e31
        | (have j1 := b0e52 X1 X0
           grind)
        | exact resolve b0e31 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e688 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e60 x (M.op y (M.op X0 X0))
           have i₂ := b0e31 X0
           grind)
        | exact superpose b0e31 b0e60
        | exact resolve b0e60 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e823 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b0e35 (M.op (σ x) (σ y)) (σ x)
           have i₂ := b0e89
           grind)
        | exact superpose b0e89 b0e35
        | exact resolve b0e35 b0e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e89
      have b0e831 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b0e823
           have i₂ := b0e36 (σ x) (σ y)
           grind)
        | exact superpose b0e36 b0e823
        | exact resolve b0e823 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e823
      have b0e839 : (M.op x y) = (k (M.op x y) x) := by grind
      clear b0e688
      have b0e2345 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e141 (M.op X0 X0) (M.op X1 (M.op X0 X0))
           have i₂ := b0e10 X0 (M.op X0 X0) X1
           grind)
        | exact superpose b0e10 b0e141
        | exact resolve b0e141 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2808 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e31 (M.op X0 (M.op X0 X0))
           have i₂ := b0e217 X0 X0 X0
           grind)
        | exact superpose b0e217 b0e31
        | exact resolve b0e31 b0e217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e2813 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op y (M.op X1 X1)) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X1 (M.op X0 (M.op X0 X0))
           have i₂ := b0e217 X0 X0 X0
           grind)
        | exact superpose b0e217 b0e40
        | exact resolve b0e40 b0e217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2828 : ∀ X0 X1 : G, x = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e216 (M.op X0 (M.op X0 X0)) X1
           have i₂ := b0e217 X0 X0 X0
           grind)
        | exact superpose b0e217 b0e216
        | exact resolve b0e216 b0e217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216 b0e217
      have b0e3809 : (M.op (σ x) (σ y)) = (M.op x (M.op y (σ x))) := by
        first
        | (have i₁ := b0e141 (σ y) (σ x)
           have i₂ := b0e831
           grind)
        | exact superpose b0e831 b0e141
        | exact resolve b0e141 b0e831
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141 b0e831
      have b0e5432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op X2 (M.op (M.op X3 X2) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e142 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X2 X3
           have i₂ := b0e10 X0 (M.op X0 X0) X1
           grind)
        | exact superpose b0e10 b0e142
        | exact resolve b0e142 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142
      have b0e5543 : ∀ X0 X2 X3 : G, (M.op x (M.op y X0)) = (M.op X2 (M.op (M.op X3 X2) X0)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e5432 X0 x X2 X3
           have i₂ := b0e2345 X0 x
           grind)
        | exact superpose b0e2345 b0e5432
        | exact resolve b0e5432 b0e2345
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2345 b0e5432
      have b0e30066 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e487 y (M.op x y) X0
           have i₂ := b0e57
           grind)
        | exact superpose b0e57 b0e487
        | (have j0 := b0e487 y (M.op x y) x
           grind)
        | exact resolve b0e487 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57 b0e487
      have b0e30520 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e30066 X0
           have i₂ := b0e86
           grind)
        | exact superpose b0e86 b0e30066
        | (have j0 := b0e30066 X0
           grind)
        | exact resolve b0e30066 b0e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86 b0e30066
      have b0e30565 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ y) (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have j0 := b0e30520 X0
           grind)
        | (have r₁ := b0e30520 X0
           have r₂ := b0e16
           grind)
        | exact resolve b0e30520 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30520
      have b0e52177 : ∀ X0 X1 : G, x = (M.op (M.op X1 X0) (M.op (M.op x (M.op y X0)) y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2828 X0 X1
           have i₂ := b0e2808 X0
           grind)
        | exact superpose b0e2808 b0e2828
        | exact resolve b0e2828 b0e2808
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2828
      have b0e57842 : ∀ X0 X1 X2 : G, (M.op x (M.op y X1)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e5543 X1 (M.op X2 (M.op X0 X0)) (M.op y (M.op X2 X2))
           have i₂ := b0e40 X2 X0
           grind)
        | exact superpose b0e40 b0e5543
        | exact resolve b0e5543 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e5543
      have b0e126887 : (σ y) = (M.op (σ (M.op x y)) (M.op x (M.op y (σ y)))) := by
        first
        | (have i₁ := b0e30565 (σ y)
           have i₂ := b0e2808 (σ y)
           grind)
        | exact superpose b0e2808 b0e30565
        | exact resolve b0e30565 b0e2808
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2808 b0e30565
      have b0e126953 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
        first
        | (have i₁ := b0e126887
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e126887
        | exact resolve b0e126887 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e126887
      have b0e127193 : (σ y) = (σ (k (M.op x y) x)) ∨ (σ (M.op x y)) = (M.op x (M.op y (σ x))) := by
        first
        | (have i₁ := b0e504 x (M.op x y)
           have i₂ := b0e126953
           grind)
        | exact superpose b0e126953 b0e504
        | (have j0 := b0e504 x (M.op x y)
           grind)
        | exact resolve b0e504 b0e126953
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e504 b0e126953
      have b0e127288 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op x (M.op y (σ x))) := by
        first
        | (have i₁ := b0e127193
           have i₂ := b0e839
           grind)
        | exact superpose b0e839 b0e127193
        | exact resolve b0e127193 b0e839
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e839 b0e127193
      have b0e127296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
        first
        | (have i₁ := b0e127288
           have i₂ := b0e3809
           grind)
        | exact superpose b0e3809 b0e127288
        | exact resolve b0e127288 b0e3809
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3809 b0e127288
      have b0e127298 : (σ (M.op x y)) = (σ y) := by
        first
        | (have r₁ := b0e127296
           have r₂ := b0e16
           grind)
        | exact resolve b0e127296 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127296
      have b0e127475 : (M.op x y) = (τ (σ y)) := by
        first
        | (have i₁ := b0e11 (M.op x y)
           have i₂ := b0e127298
           grind)
        | exact superpose b0e127298 b0e11
        | exact resolve b0e11 b0e127298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127298
      have b0e127527 : y = (M.op x y) := by
        first
        | (have i₁ := b0e127475
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e127475
        | exact resolve b0e127475 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127475
      have b0e127646 : ∀ X0 X1 : G, y = (M.op (M.op X1 X1) (M.op (M.op (M.op y (M.op X0 X0)) (M.op X0 X1)) (M.op x y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e56 (M.op X1 X1) X1
           have i₂ := b0e2813 X1 X0
           grind)
        | exact superpose b0e2813 b0e56
        | exact resolve b0e56 b0e2813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56 b0e2813
      have b0e127827 : ∀ X0 X1 : G, y = (M.op (M.op X1 X1) (M.op (M.op (M.op y (M.op X0 X0)) (M.op X0 X1)) y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e127646 X0 X1
           have i₂ := b0e127527
           grind)
        | exact superpose b0e127527 b0e127646
        | exact resolve b0e127646 b0e127527
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127527 b0e127646
      have b0e127920 : ∀ X1 : G, y = (M.op (M.op X1 X1) (M.op (M.op x (M.op y X1)) y)) := by
        intro X1
        first
        | (have i₁ := b0e127827 x X1
           have i₂ := b0e57842 x X1 y
           grind)
        | exact superpose b0e57842 b0e127827
        | exact resolve b0e127827 b0e57842
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57842 b0e127827
      have b0e127953 : x = y := by
        first
        | (have i₁ := b0e127920 x
           have i₂ := b0e52177 x x
           grind)
        | exact superpose b0e52177 b0e127920
        | exact resolve b0e127920 b0e52177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52177 b0e127920
      have b0e127973 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e127953
           grind)
        | exact superpose b0e127953 b0e16
        | exact resolve b0e16 b0e127953
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127953
      have b0e128312 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e127973
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e127973
        | exact resolve b0e127973 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127973
      have b0e128381 : False := by grind
      exact b0e128381
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
      have b1e29 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e10 X0 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 x X0 X1
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
           have i₂ := b1e10 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e33 : x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b1e29 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e29
        | exact resolve b1e29 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b1e29 (M.op y y)
           have i₂ := b1e10 y y y
           grind)
        | exact superpose b1e10 b1e29
        | exact resolve b1e29 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e35 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 (M.op y (M.op X0 X0)) x
           have i₂ := b1e29 X0
           grind)
        | exact superpose b1e29 b1e10
        | exact resolve b1e10 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29
      have b1e36 : x = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b1e33
           have i₂ := b1e34
           grind)
        | exact superpose b1e34 b1e33
        | exact resolve b1e33 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e33
      have b1e42 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e45 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b1e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b1e61 : x = (M.op (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b1e31 (M.op x y) x
           have i₂ := b1e36
           grind)
        | exact superpose b1e36 b1e31
        | exact resolve b1e31 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31 b1e36
      have b1e63 : x = (M.op y (M.op x y)) := by
        first
        | (have i₁ := b1e61
           have i₂ := b1e32 x y
           grind)
        | exact superpose b1e32 b1e61
        | exact resolve b1e61 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32 b1e61
      have b1e70 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e82 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e42 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42
      have b1e112 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e45 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e113 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e112
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e112
        | exact resolve b1e112 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e112
      have b1e114 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e113
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e113
        | exact resolve b1e113 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e113
      have b1e115 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e114
           grind)
        | exact superpose b1e114 b1e16
        | exact resolve b1e16 b1e114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e114
      have b1e376 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e46 x x
           grind)
        | exact superpose b1e46 b1e18
        | (have j1 := b1e46 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e46 x y
           grind)
        | exact resolve b1e18 b1e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e46
      have b1e498 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e70
      have b1e515 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e498 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e498
        | exact resolve b1e498 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e498
      have b1e534 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e82 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e82
        | (have j0 := b1e82 x x
           grind)
        | exact resolve b1e82 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e82
      have b1e947 : ∀ X0 : G, y = X0 ∨ (k (M.op y (M.op y y)) X0) = (M.op (M.op y (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b1e14 (M.op y (M.op y y)) X0
           have i₂ := b1e35 y y
           grind)
        | exact superpose b1e35 b1e14
        | (have j0 := b1e14 (M.op y (M.op y y)) X0
           grind)
        | exact resolve b1e14 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35
      have b1e979 : ∀ X0 : G, (M.op (M.op y (M.op x y)) X0) = (k (M.op y (M.op x y)) X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b1e947 X0
           have i₂ := b1e34
           grind)
        | exact superpose b1e34 b1e947
        | (have j0 := b1e947 X0
           grind)
        | exact resolve b1e947 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34 b1e947
      have b1e1007 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b1e979 X0
           have i₂ := b1e63
           grind)
        | exact superpose b1e63 b1e979
        | (have j0 := b1e979 X0
           grind)
        | exact resolve b1e979 b1e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e63 b1e979
      have b1e3170 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e376
           have i₂ := b1e1007 x
           grind)
        | exact superpose b1e1007 b1e376
        | (have j1 := b1e1007 x
           grind)
        | exact resolve b1e376 b1e1007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e376 b1e1007
      have b1e3183 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e3170
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e3170
        | exact resolve b1e3170 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3170
      have b1e3184 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
      clear b1e3183
      have b1e5815 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e515 x
           have i₂ := b1e3184
           grind)
        | exact superpose b1e3184 b1e515
        | exact resolve b1e515 b1e3184
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e515 b1e3184
      have b1e5889 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e5815
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e5815
        | exact resolve b1e5815 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5815
      have b1e5897 : x = (k x x) := by
        first
        | (have r₁ := b1e5889
           have r₂ := b1e534
           grind)
        | exact resolve b1e5889 b1e534
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e534 b1e5889
      have b1e6286 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e5897
           grind)
        | exact superpose b1e5897 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e5897
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e5897
      have b1e6291 : x = (M.op x x) := by grind
      clear b1e6286
      have b1e6667 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e6291
           grind)
        | exact superpose b1e6291 b1e17
        | exact resolve b1e17 b1e6291
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6291
      have b1e7309 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e115
           have i₂ := b1e6667
           grind)
        | exact superpose b1e6667 b1e115
        | exact resolve b1e115 b1e6667
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e115
      have b1e7356 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e7309
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e7309
        | exact resolve b1e7309 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7309
      have b1e7371 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e7356
           have i₂ := b1e6667
           grind)
        | exact superpose b1e6667 b1e7356
        | exact resolve b1e7356 b1e6667
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6667 b1e7356
      have b1e7372 : False := by grind
      exact b1e7372
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b2e45 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e15 X0 X1
           have i₂ := b2e14 (σ X0) (σ X1)
           grind)
        | exact superpose b2e14 b2e15
        | (have j1 := b2e14 (σ X0) (σ X1)
           grind)
        | exact resolve b2e15 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e51 : x = (M.op x y) ∨ y = (M.op x x) := by
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
      have b2e54 : x = (M.op x y) := by
        first
        | (have r₁ := b2e51
           have r₂ := b2e17
           grind)
        | exact resolve b2e51 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e474 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e49 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e49
        | exact resolve b2e49 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e855 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e474
           grind)
        | exact superpose b2e474 b2e11
        | exact resolve b2e11 b2e474
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e474
      have b2e871 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e855
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e855
        | exact resolve b2e855 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e855
      have b2e878 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e45 x x
           have i₂ := b2e871
           grind)
        | exact superpose b2e871 b2e45
        | exact resolve b2e45 b2e871
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e45 b2e871
      have b2e881 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e878
           have r₂ := b2e17
           grind)
        | exact resolve b2e878 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e878
      have b2e976 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e881
           grind)
        | exact superpose b2e881 b2e11
        | exact resolve b2e11 b2e881
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e881
      have b2e992 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e976
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e976
        | exact resolve b2e976 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e976
      have b2e993 : x = y := by grind
      clear b2e992
      have b2e1054 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e993
           grind)
        | exact superpose b2e993 b2e16
        | exact resolve b2e16 b2e993
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e1060 : x = (M.op x x) := by
        first
        | (have i₁ := b2e54
           have i₂ := b2e993
           grind)
        | exact superpose b2e993 b2e54
        | exact resolve b2e54 b2e993
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54
      have b2e1071 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e1054
           have i₂ := b2e1060
           grind)
        | exact superpose b2e1060 b2e1054
        | exact resolve b2e1054 b2e1060
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1054 b2e1060
      have b2e1073 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e1071
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e1071
        | exact resolve b2e1071 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1071
      have b2e1074 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e1073
           have i₂ := b2e993
           grind)
        | exact superpose b2e993 b2e1073
        | exact resolve b2e1073 b2e993
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e993 b2e1073
      have b2e1075 : False := by grind
      exact b2e1075
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e36 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 (σ x) X0
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 (σ x) X0
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e79 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e36 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e80 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e79
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e79
        | exact resolve b3e79 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e79
      have b3e266 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e80
           grind)
        | exact superpose b3e80 b3e16
        | exact resolve b3e16 b3e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e80
      have b3e302 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e266
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e266
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e266 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e266
      have b3e303 : y = (M.op x x) := by grind
      clear b3e302
      have b3e307 : False := by grind
      exact b3e307
