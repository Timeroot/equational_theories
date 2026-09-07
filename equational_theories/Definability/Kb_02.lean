import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4412`: `x ◇ (x ◇ y) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4412 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4412 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4412.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y y) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
      have b0e30 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e10 x X0 X3
           have i₂ := b0e10 x X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X3 (M.op X3 X0)
           have i₂ := b0e10 X3 X0 X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ y) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 y y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e34 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e34
        | exact resolve b0e34 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e37 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e33 X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e33
        | exact resolve b0e33 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (M.op X1 y)
           have i₂ := b0e36 X1
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e13 X1 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e13
        | (have j0 := b0e13 X1 X0
           have j1 := b0e14 X2 X0
           grind)
        | (have r₁ := b0e13 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e13 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 X0 (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e49 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e69 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (M.op X1 (σ y))
           have i₂ := b0e37 X1
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e72 : ∀ X1 : G, (M.op y X1) = (M.op (σ y) X1) := by
        intro X1
        first
        | (have i₁ := b0e69 x X1
           have i₂ := b0e43 x X1
           grind)
        | exact superpose b0e43 b0e69
        | exact resolve b0e69 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e81 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e14 (τ X1) X0
           grind)
        | exact superpose b0e14 b0e23
        | (have j1 := b0e14 X0 X0
           grind)
        | exact resolve b0e23 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e108 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e72 (σ y)
           grind)
        | exact superpose b0e72 b0e18
        | exact resolve b0e18 b0e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72
      have b0e167 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X0 X1 (M.op X0 y)
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e30
        | exact resolve b0e30 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e36
      have b0e439 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e55 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e55 b0e15
        | (have j1 := b0e55 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e585 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X1) ≠ (M.op X0 (M.op X0 (M.op (M.op X1 X2) X1))) ∨ (k X3 (M.op (M.op X1 X2) X1)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e13 X3 (M.op (M.op X1 X2) X1)
           have i₂ := b0e31 X1 X2 X0 (M.op (M.op X1 X2) X1)
           grind)
        | exact superpose b0e31 b0e13
        | (have j0 := b0e13 X3 (M.op (M.op X1 X2) X1)
           grind)
        | exact resolve b0e13 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e618 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X1) ≠ (M.op y (M.op (M.op X1 X2) X1)) ∨ (k X3 (M.op (M.op X1 X2) X1)) = X3 := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e585 x X1 X2 X3
           have i₂ := b0e43 x (M.op (M.op X1 X2) X1)
           grind)
        | exact superpose b0e43 b0e585
        | (have j0 := b0e585 x X1 X2 X3
           grind)
        | exact resolve b0e585 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e585
      have b0e698 : ∀ X1 X2 X3 : G, (M.op y X1) ≠ (M.op y (M.op y X1)) ∨ (k X3 (M.op (M.op X1 X2) X1)) = X3 := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e618 x X1 X3
           have i₂ := b0e167 x X1
           grind)
        | exact superpose b0e167 b0e618
        | (have j0 := b0e618 X1 X2 X3
           grind)
        | exact resolve b0e618 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e618
      have b0e762 : ∀ X1 X2 X3 : G, (k X3 (M.op (M.op X1 X2) X1)) = X3 := by
        intro X1 X2 X3
        first
        | (have j0 := b0e698 X1 X2 X3
           grind)
        | (have r₁ := b0e698 X1 X2 X3
           have r₂ := b0e43 y X1
           grind)
        | exact resolve b0e698 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e698
      have b0e803 : ∀ X1 X3 : G, (k X3 (M.op y X1)) = X3 := by
        intro X1 X3
        first
        | (have i₁ := b0e762 X1 x X3
           have i₂ := b0e167 X1 x
           grind)
        | exact superpose b0e167 b0e762
        | exact resolve b0e762 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e762
      have b0e3095 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e52 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e5203 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e81 X1 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e81
        | (have j0 := b0e81 X1 X1
           grind)
        | exact resolve b0e81 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e5305 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e5203 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e5203
        | (have j0 := b0e5203 X0 X1
           grind)
        | exact resolve b0e5203 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5203
      have b0e8181 : ∀ X0 : G, (σ (M.op y X0)) ≠ (σ (M.op y X0)) ∨ (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e3095 (M.op y X0)
           have i₂ := b0e803 X0 (M.op y X0)
           grind)
        | exact superpose b0e803 b0e3095
        | (have j0 := b0e3095 (M.op y X0)
           grind)
        | exact resolve b0e3095 b0e803
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e803
      have b0e8209 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e3095 (τ X0)
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e3095
        | (have j0 := b0e3095 (τ X0)
           grind)
        | exact resolve b0e3095 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e3095
      have b0e8234 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
        intro X0
        first
        | (have j0 := b0e8181 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8181
      have b0e8237 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e8209 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e8209
        | (have j0 := b0e8209 X0
           grind)
        | exact resolve b0e8209 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8209
      have b0e8250 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e8237 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e8237
        | (have j0 := b0e8237 X0
           grind)
        | exact resolve b0e8237 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8237
      have b0e9070 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e439 x y X0
           grind)
        | exact superpose b0e439 b0e16
        | (have j1 := b0e439 x x X0
           grind)
        | exact resolve b0e16 b0e439
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e439
      have b0e49492 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op (σ (M.op y X0)) (σ (M.op y X0))) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e31 (σ (M.op y X0)) (σ (M.op y X0)) X1 X2
           have i₂ := b0e8234 X0
           grind)
        | exact superpose b0e8234 b0e31
        | exact resolve b0e31 b0e8234
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49549 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op y X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e49492 X0 X1 X2
           have i₂ := b0e8234 X0
           grind)
        | exact superpose b0e8234 b0e49492
        | exact resolve b0e49492 b0e8234
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8234 b0e49492
      have b0e49592 : ∀ X0 X2 : G, (M.op y X2) = (M.op (σ (M.op y X0)) X2) := by
        intro X0 X2
        first
        | (have i₁ := b0e49549 X0 x X2
           have i₂ := b0e43 x X2
           grind)
        | exact superpose b0e43 b0e49549
        | exact resolve b0e49549 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49549
      have b0e60558 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e9070 X0
           have i₂ := b0e5305 y x
           grind)
        | exact superpose b0e5305 b0e9070
        | (have j0 := b0e9070 X0
           have j1 := b0e5305 X0 x
           grind)
        | (have r₁ := b0e9070 X0
           have r₂ := b0e5305 y x
           grind)
        | exact resolve b0e9070 b0e5305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5305 b0e9070
      have b0e60560 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e60558 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60558
      have b0e60660 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e99 X0 (σ x)
           have i₂ := b0e60560 (σ X0)
           grind)
        | exact superpose b0e60560 b0e99
        | exact resolve b0e99 b0e60560
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99 b0e60560
      have b0e60690 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e60660 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e60660
        | exact resolve b0e60660 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60660
      have b0e60708 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e60690 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e60690
        | exact resolve b0e60690 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60690
      have b0e60715 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e60708 X0
           have j1 := b0e13 X0 x
           grind)
        | (have r₁ := b0e60708 X0
           have r₂ := b0e13 X0 x
           grind)
        | exact resolve b0e60708 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60708
      have b0e61173 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e8250 x
           have i₂ := b0e60715 x
           grind)
        | exact superpose b0e60715 b0e8250
        | (have j0 := b0e8250 x
           grind)
        | (have r₁ := b0e8250 x
           have r₂ := b0e60715 x
           grind)
        | exact resolve b0e8250 b0e60715
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8250 b0e60715
      have b0e61233 : x = (M.op x x) := by grind
      clear b0e61173
      have b0e61806 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 x x X0 X1
           have i₂ := b0e61233
           grind)
        | exact superpose b0e61233 b0e31
        | exact resolve b0e31 b0e61233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e61814 : (M.op x x) = (M.op y x) := by
        first
        | (have i₁ := b0e167 x x
           have i₂ := b0e61233
           grind)
        | exact superpose b0e61233 b0e167
        | exact resolve b0e167 b0e61233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e167
      have b0e61854 : x = (M.op y x) := by
        first
        | (have i₁ := b0e61814
           have i₂ := b0e61233
           grind)
        | exact superpose b0e61233 b0e61814
        | exact resolve b0e61814 b0e61233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61814
      have b0e61861 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e61806 X0 X1
           have i₂ := b0e61233
           grind)
        | exact superpose b0e61233 b0e61806
        | exact resolve b0e61806 b0e61233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61233 b0e61806
      have b0e61890 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
        intro X1
        first
        | (have i₁ := b0e61861 x X1
           have i₂ := b0e43 x X1
           grind)
        | exact superpose b0e43 b0e61861
        | exact resolve b0e61861 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e61861
      have b0e62530 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e49592 x X0
           have i₂ := b0e61854
           grind)
        | exact superpose b0e61854 b0e49592
        | exact resolve b0e49592 b0e61854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49592 b0e61854
      have b0e76669 : (σ (M.op x y)) ≠ (M.op y (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e62530 (σ y)
           grind)
        | exact superpose b0e62530 b0e16
        | exact resolve b0e16 b0e62530
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62530
      have b0e76949 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e76669
           have i₂ := b0e108
           grind)
        | exact superpose b0e108 b0e76669
        | exact resolve b0e76669 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108 b0e76669
      have b0e77008 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e76949
           have i₂ := b0e61890 y
           grind)
        | exact superpose b0e61890 b0e76949
        | exact resolve b0e76949 b0e61890
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61890 b0e76949
      have b0e77035 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e77008
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e77008
        | exact resolve b0e77008 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77008
      have b0e77036 : False := by grind
      exact b0e77036
    · have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op y y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 X0 y
           grind)
        | (have r₁ := b1e13 X0 y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b1e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e21 X0 y
           have i₂ := b1e20 (τ X0)
           grind)
        | exact superpose b1e20 b1e21
        | exact resolve b1e21 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e21
      have b1e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e24 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e24
        | exact resolve b1e24 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e50 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e28 X0
           have i₂ := b1e14 X0 (σ y)
           grind)
        | exact superpose b1e14 b1e28
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | exact resolve b1e28 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e54 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e50 X0
           grind)
        | (have r₁ := b1e50 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e50 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e50 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e58 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e54 (σ y)
           grind)
        | exact superpose b1e54 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e54 (σ y)
           grind)
        | exact resolve b1e18 b1e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e64 : False := by grind
      exact b1e64
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op y y) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 X0 (σ y)
           grind)
        | (have r₁ := b2e13 X0 (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b2e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e24 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 y
           have i₂ := b2e20 (σ X0)
           grind)
        | exact superpose b2e20 b2e15
        | exact resolve b2e15 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e27 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e11 (k X0 y)
           have i₂ := b2e24 X0
           grind)
        | exact superpose b2e24 b2e11
        | exact resolve b2e11 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e28 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e27 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e27
        | exact resolve b2e27 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e49 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e28 X0
           have i₂ := b2e14 X0 y
           grind)
        | exact superpose b2e14 b2e28
        | (have j1 := b2e14 X0 y
           grind)
        | exact resolve b2e28 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e53 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e49 X0
           grind)
        | (have r₁ := b2e49 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e49 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e49 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e55 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e53 y
           grind)
        | exact superpose b2e53 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e53 y
           grind)
        | exact resolve b2e17 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53
      have b2e59 : False := by grind
      exact b2e59
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X1) := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
      have b3e23 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e10 x X0 X3
           have i₂ := b3e10 x X0 X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 X3 (M.op X3 X0)
           have i₂ := b3e10 X3 X0 X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X1 X3))) = (M.op (M.op X0 (M.op X0 X1)) (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 (M.op X1 X3) X1
           have i₂ := b3e10 X0 X1 X3
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X0 X1 x
           have i₂ := b3e10 X2 X1 x
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b3e32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13 X1 X0
           have i₂ := b3e14 X2 X0
           grind)
        | exact superpose b3e14 b3e13
        | (have j0 := b3e13 X1 X0
           have j1 := b3e14 X2 X0
           grind)
        | (have r₁ := b3e13 X0 X1
           have r₂ := b3e14 X0 X1
           grind)
        | exact resolve b3e13 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e35 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 X0 (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e36 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 X0 (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e38 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have j0 := b3e35 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35
      have b3e39 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e32 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e32
      have b3e41 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e38 (σ X0)
           grind)
        | exact superpose b3e38 b3e15
        | exact resolve b3e15 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b3e52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e30 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e30
        | exact resolve b3e30 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e56 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b3e30 X0 y
           have i₂ := b3e38 X0
           grind)
        | exact superpose b3e38 b3e30
        | exact resolve b3e30 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e30
      have b3e70 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e23 X2 X3 (M.op X2 X0)
           have i₂ := b3e10 X2 X0 X1
           grind)
        | exact superpose b3e10 b3e23
        | exact resolve b3e23 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e88 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e41 y
           grind)
        | exact superpose b3e41 b3e18
        | exact resolve b3e18 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e93 : ∀ X0 X1 : G, (M.op (σ (k X0 y)) (σ y)) = (M.op X1 (M.op X1 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X1 (σ y) (σ X0)
           have i₂ := b3e41 X0
           grind)
        | exact superpose b3e41 b3e10
        | exact resolve b3e10 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e94 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op (σ y) (σ (k X0 y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 (σ y) (σ X0) X1
           have i₂ := b3e41 X0
           grind)
        | exact superpose b3e41 b3e10
        | exact resolve b3e10 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e95 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (σ (k (k X0 y) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e94 X0 X1
           have i₂ := b3e41 (k X0 y)
           grind)
        | exact superpose b3e41 b3e94
        | exact resolve b3e94 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e94
      have b3e110 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e26 X2 (M.op X3 X1) X3
           have i₂ := b3e26 X3 X1 X0
           grind)
        | (have i₁ := b3e26 X2 (M.op X3 X1) X3
           have i₂ := b3e26 X0 X1 X3
           grind)
        | exact superpose b3e26 b3e26
        | exact resolve b3e26 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e115 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X1 X3) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e26 X2 X1 (M.op X1 X3)
           have i₂ := b3e10 X0 X1 X3
           grind)
        | exact superpose b3e10 b3e26
        | exact resolve b3e26 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e23 X2 (M.op X2 X1) X3
           have i₂ := b3e26 X2 X1 X0
           grind)
        | (have i₁ := b3e23 X2 (M.op X2 X1) X3
           have i₂ := b3e26 X0 X1 X2
           grind)
        | exact superpose b3e26 b3e23
        | exact resolve b3e23 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e128 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 X3 (M.op X3 X1)
           have i₂ := b3e26 X3 X1 X0
           grind)
        | (have i₁ := b3e10 X2 X3 (M.op X3 X1)
           have i₂ := b3e26 X0 X1 X3
           grind)
        | exact superpose b3e26 b3e10
        | exact resolve b3e10 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e129 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X2 X1) X3) (M.op X2 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 (M.op X2 X1) X3
           have i₂ := b3e26 X2 X1 X0
           grind)
        | (have i₁ := b3e10 X2 (M.op X2 X1) X3
           have i₂ := b3e26 X0 X1 X2
           grind)
        | exact superpose b3e26 b3e10
        | exact resolve b3e10 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e146 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e88
           have i₂ := b3e39 y y X0
           grind)
        | exact superpose b3e39 b3e88
        | (have j1 := b3e39 y x X0
           grind)
        | exact resolve b3e88 b3e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e88
      have b3e149 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e39 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b3e39 b3e15
        | (have j1 := b3e39 (σ X0) X2 X2
           grind)
        | exact resolve b3e15 b3e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e150 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e39 X0 X2 (τ X1)
           grind)
        | exact superpose b3e39 b3e19
        | (have j1 := b3e39 X0 X2 X2
           grind)
        | exact resolve b3e19 b3e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e153 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b3e146 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e146
      have b3e157 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X3 X4) X3) (M.op X2 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e24 X3 X4 X2 (M.op X2 X1)
           have i₂ := b3e26 X2 X1 X0
           grind)
        | (have i₁ := b3e24 X3 X4 X2 (M.op X2 X1)
           have i₂ := b3e26 X0 X1 X2
           grind)
        | exact superpose b3e26 b3e24
        | exact resolve b3e24 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e158 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X3 X4) X3) (M.op X2 X0)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e24 X3 X4 X2 (M.op X2 X0)
           have i₂ := b3e10 X2 X0 X1
           grind)
        | exact superpose b3e10 b3e24
        | exact resolve b3e24 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e161 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X3 X4) X3) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e24 X3 X4 (M.op X0 X2) X0
           have i₂ := b3e23 X0 X2 X1
           grind)
        | (have i₁ := b3e24 X3 X4 (M.op X0 X2) X0
           have i₂ := b3e23 X0 X1 X2
           grind)
        | exact superpose b3e23 b3e24
        | exact resolve b3e24 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e162 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X3 X4) X3) X1) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e24 X3 X4 (M.op X1 X2) X1
           have i₂ := b3e10 X0 X1 X2
           grind)
        | exact superpose b3e10 b3e24
        | exact resolve b3e24 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e169 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X3 X4)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X5) X4) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e24 X5 (M.op X5 X2) X3 X4
           have i₂ := b3e24 X0 X1 X5 X2
           grind)
        | exact superpose b3e24 b3e24
        | exact resolve b3e24 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e198 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e23 X3 X4 (M.op X3 X2)
           have i₂ := b3e24 X0 X1 X3 X2
           grind)
        | exact superpose b3e24 b3e23
        | exact resolve b3e23 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e200 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X4 X2))) = (M.op X4 (M.op (M.op (M.op X0 X1) X0) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e26 X3 (M.op X4 X2) X4
           have i₂ := b3e24 X0 X1 X4 X2
           grind)
        | exact superpose b3e24 b3e26
        | exact resolve b3e26 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e206 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op X1 X4) X1) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 (M.op (M.op X2 X3) X2) X1 X4
           have i₂ := b3e24 X2 X3 X0 X1
           grind)
        | exact superpose b3e24 b3e10
        | exact resolve b3e10 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e211 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op (M.op X3 X4) X3) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e26 X2 X1 (M.op (M.op X3 X4) X3)
           have i₂ := b3e24 X3 X4 X0 X1
           grind)
        | exact superpose b3e24 b3e26
        | exact resolve b3e26 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e218 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e153 (τ X0)
           grind)
        | exact superpose b3e153 b3e19
        | exact resolve b3e19 b3e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e220 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e218 X0
           have i₂ := b3e38 X0
           grind)
        | exact superpose b3e38 b3e218
        | exact resolve b3e218 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38 b3e218
      have b3e775 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X3 X4)) = (M.op (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X1 X2)) X5) X4) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e24 X5 (M.op X5 (M.op X1 X2)) X3 X4
           have i₂ := b3e25 X0 X1 X5 X2
           grind)
        | exact superpose b3e25 b3e24
        | exact resolve b3e24 b3e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24 b3e25
      have b3e865 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e13 X1 (σ X0)
           have i₂ := b3e36 X0 X0
           grind)
        | exact superpose b3e36 b3e13
        | (have j0 := b3e13 X1 (σ X0)
           have j1 := b3e36 X0 X1
           grind)
        | (have r₁ := b3e13 X0 (σ X0)
           have r₂ := b3e36 X0 X1
           grind)
        | exact resolve b3e13 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e911 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e36 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e928 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b3e865 X0 X1
           have j1 := b3e13 X1 (σ X0)
           grind)
        | (have r₁ := b3e865 X0 X1
           have r₂ := b3e13 X0 (σ X0)
           grind)
        | exact resolve b3e865 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e865
      have b3e1009 : ∀ X0 X1 : G, (k (τ (M.op (σ y) X1)) y) = (τ (M.op X0 (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e56 (M.op (σ y) X1)
           have i₂ := b3e26 (σ y) X1 X0
           grind)
        | (have i₁ := b3e56 (M.op (σ y) X1)
           have i₂ := b3e26 X0 X1 (σ y)
           grind)
        | exact superpose b3e26 b3e56
        | exact resolve b3e56 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1027 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op y (τ (M.op (σ y) X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e1009 X0 X1
           have i₂ := b3e153 (τ (M.op (σ y) X1))
           grind)
        | exact superpose b3e153 b3e1009
        | exact resolve b3e1009 b3e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1009
      have b3e1034 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op y (k (τ X1) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e1027 X0 X1
           have i₂ := b3e56 X1
           grind)
        | exact superpose b3e56 b3e1027
        | exact resolve b3e1027 b3e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e56 b3e1027
      have b3e1040 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op y (M.op y (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e1034 X0 X1
           have i₂ := b3e153 (τ X1)
           grind)
        | exact superpose b3e153 b3e1034
        | exact resolve b3e1034 b3e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1034
      have b3e1066 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 y)) (σ y)) = (M.op (M.op (M.op X1 X2) X1) (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e70 X1 X2 (σ y) (σ X0)
           have i₂ := b3e41 X0
           grind)
        | exact superpose b3e41 b3e70
        | exact resolve b3e70 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e41
      have b3e1082 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 (M.op X0 X1)) X4) X2) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e70 X4 (M.op X4 X1) X2 X3
           have i₂ := b3e26 X4 X1 X0
           grind)
        | (have i₁ := b3e70 X4 (M.op X4 X1) X2 X3
           have i₂ := b3e26 X0 X1 X4
           grind)
        | exact superpose b3e26 b3e70
        | exact resolve b3e70 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1191 : ∀ X0 X1 X2 : G, (M.op (σ (M.op y X0)) (σ y)) = (M.op (M.op (M.op X1 X2) X1) (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1066 X0 X1 X2
           have i₂ := b3e153 X0
           grind)
        | exact superpose b3e153 b3e1066
        | exact resolve b3e1066 b3e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1066
      have b3e1263 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X4 (M.op X4 X5)) X2) := by
        intro X0 X1 X2 X4 X5
        first
        | (have i₁ := b3e127 X4 X5 X2 x
           have i₂ := b3e127 X0 X1 X2 x
           grind)
        | (have i₁ := b3e127 X0 X1 X2 (M.op X2 X1)
           have i₂ := b3e127 X2 X1 X2 x
           grind)
        | exact superpose b3e127 b3e127
        | exact resolve b3e127 b3e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1492 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X4 (M.op X0 (M.op X0 X1))) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e128 X4 (M.op X4 X1) X2 X3
           have i₂ := b3e26 X4 X1 X0
           grind)
        | (have i₁ := b3e128 X4 (M.op X4 X1) X2 X3
           have i₂ := b3e26 X0 X1 X4
           grind)
        | exact superpose b3e26 b3e128
        | exact resolve b3e128 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e128
      have b3e1867 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e928 (τ X0) X1
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e928
        | (have j0 := b3e928 (τ X0) X1
           grind)
        | exact resolve b3e928 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e928
      have b3e1877 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1867 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1867
        | (have j0 := b3e1867 X0 X1
           grind)
        | exact resolve b3e1867 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1867
      have b3e1882 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1877 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1877
        | (have j0 := b3e1877 X0 X1
           grind)
        | exact resolve b3e1877 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1877
      have b3e1902 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1882 (τ X0) X1
           have i₂ := b3e52 X0 X0
           grind)
        | exact superpose b3e52 b3e1882
        | (have j0 := b3e1882 (τ X0) X1
           grind)
        | exact resolve b3e1882 b3e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e52 b3e1882
      have b3e2111 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e220 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e220
        | exact resolve b3e220 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e220
      have b3e2338 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op (σ (M.op y X0)) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e23 (σ y) X1 (σ X0)
           have i₂ := b3e2111 X0
           grind)
        | exact superpose b3e2111 b3e23
        | exact resolve b3e23 b3e2111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23
      have b3e2368 : ∀ X0 : G, (M.op (σ (M.op y X0)) (σ y)) = (σ (k (k y y) y)) := by
        intro X0
        first
        | (have i₁ := b3e2338 X0 x
           have i₂ := b3e95 y x
           grind)
        | exact superpose b3e95 b3e2338
        | exact resolve b3e2338 b3e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e95 b3e2338
      have b3e2389 : ∀ X0 : G, (M.op (σ (M.op y X0)) (σ y)) = (σ (M.op y (k y y))) := by
        intro X0
        first
        | (have i₁ := b3e2368 X0
           have i₂ := b3e153 (k y y)
           grind)
        | exact superpose b3e153 b3e2368
        | exact resolve b3e2368 b3e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2368
      have b3e2399 : ∀ X0 : G, (M.op (σ (M.op y X0)) (σ y)) = (σ (M.op y (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b3e2389 X0
           have i₂ := b3e153 y
           grind)
        | exact superpose b3e153 b3e2389
        | exact resolve b3e2389 b3e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2389
      have b3e4574 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e150 X1 (σ X0) X2
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e150
        | (have j0 := b3e150 X1 X1 X2
           grind)
        | exact resolve b3e150 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e150
      have b3e4679 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e4574 X0 X1 X2
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e4574
        | (have j0 := b3e4574 X0 X1 X2
           grind)
        | exact resolve b3e4574 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4574
      have b3e9802 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e911 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e911
        | (have j0 := b3e911 (τ X0)
           grind)
        | exact resolve b3e911 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20 b3e911
      have b3e9828 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e9802 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e9802
        | (have j0 := b3e9802 X0
           grind)
        | exact resolve b3e9802 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e9802
      have b3e9838 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e9828 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e9828
        | (have j0 := b3e9828 X0
           grind)
        | exact resolve b3e9828 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e9828
      have b3e10881 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e49 X0 (σ X1)
           have i₂ := b3e149 X1 X2 (σ X0)
           grind)
        | exact superpose b3e149 b3e49
        | (have j1 := b3e149 X1 X2 X2
           grind)
        | exact resolve b3e49 b3e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e49 b3e149
      have b3e10890 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10881 X0 X1 X2
           have i₂ := b3e11 X1
           grind)
        | exact superpose b3e11 b3e10881
        | (have j0 := b3e10881 X0 X1 X2
           grind)
        | exact resolve b3e10881 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e10881
      have b3e10922 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10890 X0 X1 X2
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e10890
        | (have j0 := b3e10890 X0 X1 X2
           grind)
        | exact resolve b3e10890 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e10890
      have b3e13950 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X3) X1)) = (M.op (M.op (σ (M.op y X0)) (σ y)) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e161 X1 X3 X2 (σ y) (σ X0)
           have i₂ := b3e2111 X0
           grind)
        | exact superpose b3e2111 b3e161
        | exact resolve b3e161 b3e2111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e161
      have b3e14310 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X3) X1)) = (M.op (σ (M.op y (M.op y y))) X1) := by
        intro X1 X2 X3
        first
        | (have i₁ := b3e13950 x X1 X2 X3
           have i₂ := b3e2399 x
           grind)
        | exact superpose b3e2399 b3e13950
        | exact resolve b3e13950 b3e2399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13950
      have b3e14686 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 (M.op X3 X1))) = (M.op (M.op (σ (M.op y X0)) (σ y)) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e162 X3 X1 X2 (σ y) (σ X0)
           have i₂ := b3e2111 X0
           grind)
        | exact superpose b3e2111 b3e162
        | exact resolve b3e162 b3e2111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e162 b3e2111
      have b3e15100 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 (M.op X3 X1))) = (M.op (σ (M.op y (M.op y y))) X1) := by
        intro X1 X2 X3
        first
        | (have i₁ := b3e14686 x X1 X2 X3
           have i₂ := b3e2399 x
           grind)
        | exact superpose b3e2399 b3e14686
        | exact resolve b3e14686 b3e2399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14686
      have b3e15951 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 X6) (M.op X7 (M.op X7 X5))) = (M.op X0 (M.op X0 (M.op (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X5))) := by
        intro X0 X1 X2 X3 X4 X5 X6 X7
        first
        | (have i₁ := b3e115 X7 X5 (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X6
           have i₂ := b3e169 X1 X2 X3 X0 (M.op (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X5) X4
           grind)
        | exact superpose b3e169 b3e115
        | exact resolve b3e115 b3e169
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e115
      have b3e16007 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (σ (M.op y (M.op y y))) X5) = (M.op X0 (M.op X0 (M.op (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X5))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e15951 X0 X1 X2 X3 X4 X5 x x
           have i₂ := b3e15100 X5 x x
           grind)
        | exact superpose b3e15100 b3e15951
        | exact resolve b3e15951 b3e15100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e15100 b3e15951
      have b3e17832 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X2) X1) (M.op X5 (M.op X5 X3))) = (M.op X0 (M.op X0 (M.op (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X3))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e129 X5 X3 (M.op (M.op X1 X2) X1) X4
           have i₂ := b3e200 X1 X2 X3 X0 (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4)
           grind)
        | exact superpose b3e200 b3e129
        | exact resolve b3e129 b3e200
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e129
      have b3e17844 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X5 X6) X5) (M.op (M.op (M.op X1 X2) X1) X3)) = (M.op X0 (M.op X0 (M.op (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X3))) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b3e70 X5 X6 (M.op (M.op (M.op X1 X2) X1) X3) X4
           have i₂ := b3e200 X1 X2 X3 X0 (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4)
           grind)
        | exact superpose b3e200 b3e70
        | exact resolve b3e70 b3e200
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e70 b3e200
      have b3e17938 : ∀ X1 X2 X3 X5 X6 : G, (M.op (σ (M.op y (M.op y y))) X3) = (M.op (M.op (M.op X5 X6) X5) (M.op (M.op (M.op X1 X2) X1) X3)) := by
        intro X1 X2 X3 X5 X6
        first
        | (have i₁ := b3e17844 x X1 X2 X3 x X5 X6
           have i₂ := b3e16007 x X1 X2 X3 x X3
           grind)
        | exact superpose b3e16007 b3e17844
        | exact resolve b3e17844 b3e16007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e17844
      have b3e17946 : ∀ X1 X2 X3 X5 : G, (M.op (M.op (M.op X1 X2) X1) (M.op X5 (M.op X5 X3))) = (M.op (σ (M.op y (M.op y y))) X3) := by
        intro X1 X2 X3 X5
        first
        | (have i₁ := b3e17832 x X1 X2 X3 x X5
           have i₂ := b3e16007 x X1 X2 X3 x X3
           grind)
        | exact superpose b3e16007 b3e17832
        | exact resolve b3e17832 b3e16007
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e16007 b3e17832
      have b3e19006 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X3 X4) (M.op (M.op X3 X5) X3)) = (M.op (M.op (M.op X6 X7) X6) (M.op (M.op (M.op X0 X1) X0) (M.op X2 (M.op X2 X3)))) := by
        intro X0 X1 X2 X3 X4 X5 X6 X7
        first
        | (have i₁ := b3e158 X3 X5 (M.op X3 X4) X6 X7
           have i₂ := b3e206 X2 X3 X0 X1 X4
           grind)
        | exact superpose b3e206 b3e158
        | exact resolve b3e158 b3e206
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e158 b3e206
      have b3e19107 : ∀ X2 X3 X4 X5 : G, (M.op (M.op X3 X4) (M.op (M.op X3 X5) X3)) = (M.op (σ (M.op y (M.op y y))) (M.op X2 (M.op X2 X3))) := by
        intro X2 X3 X4 X5
        first
        | (have i₁ := b3e19006 x x X2 X3 X4 X5 x x
           have i₂ := b3e17938 x x (M.op X2 (M.op X2 X3)) x x
           grind)
        | exact superpose b3e17938 b3e19006
        | exact resolve b3e19006 b3e17938
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e17938 b3e19006
      have b3e19232 : ∀ X2 X3 : G, (M.op (σ (M.op y (M.op y y))) X3) = (M.op (σ (M.op y (M.op y y))) (M.op X2 (M.op X2 X3))) := by
        intro X2 X3
        first
        | (have i₁ := b3e19107 X2 X3 x x
           have i₂ := b3e14310 X3 x x
           grind)
        | exact superpose b3e14310 b3e19107
        | exact resolve b3e19107 b3e14310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14310 b3e19107
      have b3e19510 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) = (M.op (M.op (M.op X4 X5) X4) (M.op X6 (M.op X6 (M.op X3 (M.op X3 X2))))) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b3e211 X6 (M.op X3 (M.op X3 X2)) X1 X4 X5
           have i₂ := b3e110 X3 X2 X0 X1
           grind)
        | (have i₁ := b3e211 X0 (M.op X2 (M.op X3 X1)) X2 X3 X4
           have i₂ := b3e110 X0 X1 X2 X3
           grind)
        | exact superpose b3e110 b3e211
        | exact resolve b3e211 b3e110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e110
      have b3e20109 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 (M.op X3 (M.op X2 X1)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e157 X3 (M.op X2 X1) X2 x x
           have i₂ := b3e211 X2 X1 X0 x x
           grind)
        | exact superpose b3e211 b3e157
        | exact resolve b3e157 b3e211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e157 b3e211
      have b3e20524 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) = (M.op (σ (M.op y (M.op y y))) (M.op X3 (M.op X3 X2))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e19510 X0 X1 X2 X3 x x x
           have i₂ := b3e17946 x x (M.op X3 (M.op X3 X2)) x
           grind)
        | exact superpose b3e17946 b3e19510
        | exact resolve b3e19510 b3e17946
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e17946 b3e19510
      have b3e20601 : ∀ X0 X1 X2 : G, (M.op (σ (M.op y (M.op y y))) X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e20524 X0 X1 X2 x
           have i₂ := b3e19232 x X2
           grind)
        | (have i₁ := b3e20524 X0 X1 X2 x
           have i₂ := b3e19232 X2 (M.op x (M.op x X2))
           grind)
        | exact superpose b3e19232 b3e20524
        | exact resolve b3e20524 b3e19232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19232 b3e20524
      have b3e39362 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (σ (M.op y (M.op y (τ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b3e12 (M.op X1 (M.op X1 X0))
           have i₂ := b3e1040 X1 X0
           grind)
        | exact superpose b3e1040 b3e12
        | exact resolve b3e12 b3e1040
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1040
      have b3e74726 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e39362 X1 X2
           have i₂ := b3e26 y (τ X1) X0
           grind)
        | (have i₁ := b3e39362 X1 X2
           have i₂ := b3e26 X0 (τ X1) y
           grind)
        | exact superpose b3e26 b3e39362
        | exact resolve b3e39362 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26 b3e39362
      have b3e92969 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X2 (M.op X2 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e74726 X2 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e74726
        | exact resolve b3e74726 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e74726
      have b3e131482 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e198 x x (M.op (M.op (M.op x x) x) (σ X1)) X2 X3
           have i₂ := b3e92969 X1 (M.op (M.op x x) x) X0
           grind)
        | exact superpose b3e92969 b3e198
        | exact resolve b3e198 b3e92969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e198
      have b3e131519 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (σ (M.op X0 (M.op X0 X1))) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e775 x x x X2 X3 (M.op (M.op (M.op x (M.op x x)) (M.op x x)) (σ X1))
           have i₂ := b3e92969 X1 (M.op (M.op x (M.op x x)) (M.op x x)) X0
           grind)
        | exact superpose b3e92969 b3e775
        | exact resolve b3e775 b3e92969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e775 b3e92969
      have b3e605871 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e10922 X0 x y
           grind)
        | exact superpose b3e10922 b3e16
        | (have j1 := b3e10922 X0 x x
           grind)
        | exact resolve b3e16 b3e10922
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e10922
      have b3e605913 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e605871 X0
           have j1 := b3e4679 X0 x X0
           grind)
        | (have r₁ := b3e605871 X0
           have r₂ := b3e4679 y x x
           grind)
        | exact resolve b3e605871 b3e4679
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4679 b3e605871
      have b3e610853 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (k X0 (τ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e1902 x X0
           have i₂ := b3e605913 x
           grind)
        | exact superpose b3e605913 b3e1902
        | (have j0 := b3e1902 x X0
           grind)
        | exact resolve b3e1902 b3e605913
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1902
      have b3e610854 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e9838 x
           have i₂ := b3e605913 x
           grind)
        | exact superpose b3e605913 b3e9838
        | (have j0 := b3e9838 x
           grind)
        | (have r₁ := b3e9838 x
           have r₂ := b3e605913 x
           grind)
        | exact resolve b3e9838 b3e605913
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e605913
      have b3e610906 : x = (M.op x x) := by grind
      clear b3e610854
      have b3e610907 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
        intro X0
        first
        | (have j0 := b3e610853 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e610853
      have b3e615972 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op (M.op x x) X2) X3) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e169 x x X2 X0 X1 X3
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e169
        | exact resolve b3e169 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e169
      have b3e616105 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x x) X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1082 x x X0 X1 X2
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e1082
        | exact resolve b3e1082 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1082
      have b3e616111 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op x x) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1263 X0 X1 X2 x x
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e1263
        | exact resolve b3e1263 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1263
      have b3e616121 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 (M.op x x)) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1492 x x X0 X1 X2
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e1492
        | exact resolve b3e1492 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1492
      have b3e616219 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ (M.op x x)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e131482 x x X0 X1
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e131482
        | exact resolve b3e131482 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e131482
      have b3e616220 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ (M.op x x)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e131519 x x X0 X1
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e131519
        | exact resolve b3e131519 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e131519
      have b3e616232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e616220 X0 X1
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e616220
        | exact resolve b3e616220 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616220
      have b3e616233 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e616219 X0 X1
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e616219
        | exact resolve b3e616219 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616219
      have b3e616328 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 x) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e616121 X0 X1 X2
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e616121
        | exact resolve b3e616121 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616121
      have b3e616336 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op x X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e616111 X0 X1 X2
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e616111
        | exact resolve b3e616111 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616111
      have b3e616341 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e616105 X0 X1 X2
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e616105
        | exact resolve b3e616105 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616105
      have b3e616427 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op x X2) X3) X1) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e615972 X0 X1 X2 X3
           have i₂ := b3e610906
           grind)
        | exact superpose b3e610906 b3e615972
        | exact resolve b3e615972 b3e610906
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e610906 b3e615972
      have b3e616469 : ∀ X1 X2 : G, (M.op (σ x) X1) = (M.op (M.op X2 x) X1) := by
        intro X1 X2
        first
        | (have i₁ := b3e616328 x X1 X2
           have i₂ := b3e616232 x X1
           grind)
        | exact superpose b3e616232 b3e616328
        | exact resolve b3e616328 b3e616232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616328
      have b3e616471 : ∀ X1 X2 : G, (M.op x X2) = (M.op (M.op (σ x) X1) X2) := by
        intro X1 X2
        first
        | (have i₁ := b3e616336 x X1 X2
           have i₂ := b3e616232 x X1
           grind)
        | exact superpose b3e616232 b3e616336
        | exact resolve b3e616336 b3e616232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616336
      have b3e616474 : ∀ X0 X2 : G, (M.op (σ x) X0) = (M.op (M.op x X2) X0) := by
        intro X0 X2
        first
        | (have i₁ := b3e616341 X0 x X2
           have i₂ := b3e616233 X0 x
           grind)
        | exact superpose b3e616233 b3e616341
        | exact resolve b3e616341 b3e616233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616233 b3e616341
      have b3e616517 : ∀ X1 X2 X3 : G, (M.op (σ x) X1) = (M.op (M.op (M.op x X2) X3) X1) := by
        intro X1 X2 X3
        first
        | (have i₁ := b3e616427 x X1 X2 X3
           have i₂ := b3e616232 x X1
           grind)
        | exact superpose b3e616232 b3e616427
        | exact resolve b3e616427 b3e616232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616427
      have b3e616560 : ∀ X1 X3 : G, (M.op (σ x) X1) = (M.op (M.op (σ x) X3) X1) := by
        intro X1 X3
        first
        | (have i₁ := b3e616517 X1 x X3
           have i₂ := b3e616474 X3 x
           grind)
        | exact superpose b3e616474 b3e616517
        | exact resolve b3e616517 b3e616474
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616474 b3e616517
      have b3e616586 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) := by
        intro X1
        first
        | (have i₁ := b3e616560 X1 x
           have i₂ := b3e616471 x X1
           grind)
        | exact superpose b3e616471 b3e616560
        | exact resolve b3e616560 b3e616471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616560
      have b3e626021 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
        first
        | (have i₁ := b3e9838 (τ x)
           have i₂ := b3e610907 (τ x)
           grind)
        | exact superpose b3e610907 b3e9838
        | (have j0 := b3e9838 (τ x)
           grind)
        | (have r₁ := b3e9838 (τ x)
           have r₂ := b3e610907 (τ x)
           grind)
        | exact resolve b3e9838 b3e610907
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e9838 b3e610907
      have b3e626058 : (τ x) = (M.op (τ x) (τ x)) := by grind
      clear b3e626021
      have b3e694120 : ∀ X0 X1 : G, (M.op (τ x) (τ x)) = (M.op (M.op X0 (M.op X0 X1)) (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b3e127 X0 X1 (τ x) (τ x)
           have i₂ := b3e626058
           grind)
        | exact superpose b3e626058 b3e127
        | exact resolve b3e127 b3e626058
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e127
      have b3e694502 : ∀ X1 : G, (M.op (τ x) (τ x)) = (M.op (M.op (σ x) X1) (τ x)) := by
        intro X1
        first
        | (have i₁ := b3e694120 x X1
           have i₂ := b3e616232 x X1
           grind)
        | exact superpose b3e616232 b3e694120
        | exact resolve b3e694120 b3e616232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e694120
      have b3e694643 : (M.op (τ x) (τ x)) = (M.op x (τ x)) := by
        first
        | (have i₁ := b3e694502 x
           have i₂ := b3e616471 x (τ x)
           grind)
        | exact superpose b3e616471 b3e694502
        | exact resolve b3e694502 b3e616471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616471 b3e694502
      have b3e694737 : (τ x) = (M.op x (τ x)) := by
        first
        | (have i₁ := b3e694643
           have i₂ := b3e626058
           grind)
        | exact superpose b3e626058 b3e694643
        | exact resolve b3e694643 b3e626058
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e626058 b3e694643
      have b3e694828 : ∀ X0 X2 X3 : G, (M.op (σ (k X0 y)) (σ y)) = (M.op X2 (M.op X3 (M.op X3 (M.op X2 (σ y))))) := by
        intro X0 X2 X3
        first
        | (have i₁ := b3e20109 x (σ y) X2 X3
           have i₂ := b3e93 X0 x
           grind)
        | exact superpose b3e93 b3e20109
        | exact resolve b3e20109 b3e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e93 b3e20109
      have b3e695785 : ∀ X0 : G, (M.op (σ (k X0 y)) (σ y)) = (M.op (σ (M.op y (M.op y y))) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e694828 X0 x x
           have i₂ := b3e20601 x x (σ y)
           grind)
        | exact superpose b3e20601 b3e694828
        | exact resolve b3e694828 b3e20601
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20601 b3e694828
      have b3e695829 : ∀ X0 : G, (M.op (σ (k X0 y)) (σ y)) = (σ (M.op y (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b3e695785 X0
           have i₂ := b3e2399 (M.op y y)
           grind)
        | exact superpose b3e2399 b3e695785
        | exact resolve b3e695785 b3e2399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2399 b3e695785
      have b3e695861 : ∀ X0 : G, (M.op (σ (k X0 y)) (σ y)) = (σ (M.op (σ x) y)) := by
        intro X0
        first
        | (have i₁ := b3e695829 X0
           have i₂ := b3e616232 y y
           grind)
        | exact superpose b3e616232 b3e695829
        | exact resolve b3e695829 b3e616232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616232 b3e695829
      have b3e695886 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (k X0 y)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e695861 X0
           have i₂ := b3e616586 y
           grind)
        | exact superpose b3e616586 b3e695861
        | exact resolve b3e695861 b3e616586
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616586 b3e695861
      have b3e695910 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op y X0)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e695886 X0
           have i₂ := b3e153 X0
           grind)
        | exact superpose b3e153 b3e695886
        | exact resolve b3e695886 b3e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e153 b3e695886
      have b3e697067 : ∀ X0 : G, (M.op (σ (M.op y X0)) (σ y)) = (M.op (M.op (τ x) x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e1191 X0 x (τ x)
           have i₂ := b3e694737
           grind)
        | exact superpose b3e694737 b3e1191
        | exact resolve b3e1191 b3e694737
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1191 b3e694737
      have b3e697278 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op y X0)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e697067 X0
           have i₂ := b3e616469 (σ y) (τ x)
           grind)
        | exact superpose b3e616469 b3e697067
        | exact resolve b3e697067 b3e616469
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e616469 b3e697067
      have b3e697315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e697278 x
           have i₂ := b3e695910 x
           grind)
        | exact superpose b3e695910 b3e697278
        | exact resolve b3e697278 b3e695910
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e695910 b3e697278
      have b3e697331 : False := by grind
      exact b3e697331

/-- `Equation4416`: `x ◇ (x ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4416 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4416 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4416.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
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
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X2)) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 (M.op X1 X2) X3
           have i₂ := b0e10 X1 X2 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) (σ x) X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) X0) := by
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
      have b0e38 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y X0) := by
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
      have b0e40 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
        intro X0 X1
        grind
      have b0e41 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e38 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 (M.op x X0)
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e38
        | exact resolve b0e38 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b0e56 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 x X0 y
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e10
        | exact resolve b0e10 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e56 X0
           have i₂ := b0e10 y X0 x
           grind)
        | exact superpose b0e10 b0e56
        | exact resolve b0e56 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e58 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e57 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e57
        | exact resolve b0e57 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e60 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
      have b0e65 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e68 : (M.op x y) = (M.op y (M.op x y)) := by
        first
        | (have i₁ := b0e58 x
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e58
        | exact resolve b0e58 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : (M.op x y) = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b0e68
           have i₂ := b0e42 y
           grind)
        | exact superpose b0e42 b0e68
        | exact resolve b0e68 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e127 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e37 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e37
        | exact resolve b0e37 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e128 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e37 (M.op (σ x) X0)
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e37
        | exact resolve b0e37 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e173 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
        first
        | (have i₁ := b0e33 (M.op x (σ x))
           have i₂ := b0e33 x
           grind)
        | exact superpose b0e33 b0e33
        | exact resolve b0e33 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e195 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b0e173
           have i₂ := b0e10 (σ y) (σ x) (σ x)
           grind)
        | exact superpose b0e10 b0e173
        | exact resolve b0e173 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e173
      have b0e201 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b0e195
           have i₂ := b0e127
           grind)
        | exact superpose b0e127 b0e195
        | exact resolve b0e195 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e195
      have b0e202 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
        first
        | (have i₁ := b0e201
           have i₂ := b0e128 (σ y)
           grind)
        | exact superpose b0e128 b0e201
        | exact resolve b0e201 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e201
      have b0e207 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e65
      have b0e221 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e207 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e207
        | exact resolve b0e207 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e207
      have b0e405 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X2 ∨ (M.op (M.op X0 X0) X2) = (k (M.op X0 X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 (M.op X0 X0) X2
           have i₂ := b0e31 X1 X0 X0 X0
           grind)
        | exact superpose b0e31 b0e14
        | (have j0 := b0e14 (M.op X0 X0) X2
           grind)
        | exact resolve b0e14 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e430 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (k (M.op X0 X0) X2) ∨ (M.op X0 (M.op (M.op X1 X0) X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e405 X0 X1 X2
           have i₂ := b0e10 X0 X2 X0
           grind)
        | exact superpose b0e10 b0e405
        | (have j0 := b0e405 X0 X1 X2
           grind)
        | exact resolve b0e405 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e405
      have b0e870 : (M.op x y) = (k (M.op x y) (M.op y (M.op x (M.op y y)))) := by
        first
        | (have i₁ := b0e40 y x
           have i₂ := b0e42 y
           grind)
        | exact superpose b0e42 b0e40
        | exact resolve b0e40 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e890 : (M.op x y) = (k (M.op x y) (M.op x (M.op y (M.op y y)))) := by
        first
        | (have i₁ := b0e870
           have i₂ := b0e42 (M.op y y)
           grind)
        | exact superpose b0e42 b0e870
        | exact resolve b0e870 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e870
      have b0e904 : (M.op x y) = (k (M.op x y) (M.op x (M.op y y))) := by
        first
        | (have i₁ := b0e890
           have i₂ := b0e58 y
           grind)
        | exact superpose b0e58 b0e890
        | exact resolve b0e890 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e890
      have b0e910 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e904
           have i₂ := b0e70
           grind)
        | exact superpose b0e70 b0e904
        | exact resolve b0e904 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70 b0e904
      have b0e1643 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ y) (σ x) X0
           have i₂ := b0e127
           grind)
        | exact superpose b0e127 b0e10
        | exact resolve b0e10 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1671 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (M.op X0 (σ y)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e1643 X0
           have i₂ := b0e128 (σ y)
           grind)
        | exact superpose b0e128 b0e1643
        | exact resolve b0e1643 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128 b0e1643
      have b0e1686 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e1671 X0
           have i₂ := b0e202
           grind)
        | exact superpose b0e202 b0e1671
        | exact resolve b0e1671 b0e202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e202 b0e1671
      have b0e1798 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 (σ X0) (σ X1) X2
           have i₂ := b0e53 X0 X1
           grind)
        | exact superpose b0e53 b0e10
        | (have j1 := b0e53 X0 X1
           grind)
        | exact resolve b0e10 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1828 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e221 X1
           have i₂ := b0e53 X1 X0
           grind)
        | exact superpose b0e53 b0e221
        | (have j1 := b0e53 X1 X0
           grind)
        | exact resolve b0e221 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e221
      have b0e1850 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e53 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e1853 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1828 X0 X1
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e1828
        | (have j0 := b0e1828 X0 X1
           grind)
        | exact resolve b0e1828 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1828
      have b0e10734 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e1850 (M.op x y)
           have i₂ := b0e910
           grind)
        | exact superpose b0e910 b0e1850
        | (have j0 := b0e1850 (M.op x y)
           grind)
        | exact resolve b0e1850 b0e910
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e910 b0e1850
      have b0e10753 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e10734
      have b0e10863 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e60 X0 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e60
        | exact resolve b0e60 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e11017 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e10863 X0 X1
           have i₂ := b0e15 X1 X0
           grind)
        | exact superpose b0e15 b0e10863
        | (have j0 := b0e10863 X0 X1
           grind)
        | exact resolve b0e10863 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10863
      have b0e11129 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      clear b0e11017
      have b0e170366 : ∀ X0 X1 : G, (M.op x X0) = (M.op y (M.op (M.op X1 x) x)) ∨ (M.op x (M.op x X0)) = (k (M.op x x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e38 (M.op (M.op X1 x) x)
           have i₂ := b0e430 x X1 X0
           grind)
        | (have i₁ := b0e38 X0
           have i₂ := b0e430 X0 X1 (M.op x X0)
           grind)
        | exact superpose b0e430 b0e38
        | (have j1 := b0e430 x X1 X0
           grind)
        | exact resolve b0e38 b0e430
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e430
      have b0e170393 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op x (M.op x x))) ∨ (M.op x (M.op x X0)) = (k (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b0e170366 X0 x
           have i₂ := b0e10 x x x
           grind)
        | exact superpose b0e10 b0e170366
        | (have j0 := b0e170366 X0 x
           grind)
        | exact resolve b0e170366 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170366
      have b0e170465 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op y (M.op x x))) ∨ (M.op x (M.op x X0)) = (k (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b0e170393 X0
           have i₂ := b0e42 (M.op x x)
           grind)
        | exact superpose b0e42 b0e170393
        | (have j0 := b0e170393 X0
           grind)
        | exact resolve b0e170393 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170393
      have b0e170488 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x (M.op y x))) ∨ (M.op x (M.op x X0)) = (k (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b0e170465 X0
           have i₂ := b0e42 x
           grind)
        | exact superpose b0e42 b0e170465
        | (have j0 := b0e170465 X0
           grind)
        | exact resolve b0e170465 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e170465
      have b0e170503 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op y x)) ∨ (M.op x (M.op x X0)) = (k (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b0e170488 X0
           have i₂ := b0e38 (M.op y x)
           grind)
        | exact superpose b0e38 b0e170488
        | (have j0 := b0e170488 X0
           grind)
        | exact resolve b0e170488 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170488
      have b0e170510 : ∀ X0 : G, (M.op x X0) = (M.op y x) ∨ (M.op x (M.op x X0)) = (k (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b0e170503 X0
           have i₂ := b0e58 x
           grind)
        | exact superpose b0e58 b0e170503
        | (have j0 := b0e170503 X0
           grind)
        | exact resolve b0e170503 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58 b0e170503
      have b0e170516 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (M.op x (M.op x X0)) = (k (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b0e170510 X0
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e170510
        | (have j0 := b0e170510 X0
           grind)
        | exact resolve b0e170510 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170510
      have b0e170522 : ∀ X0 : G, (M.op x (M.op x X0)) = (k y X0) ∨ (M.op x y) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e170516 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e170516
        | (have j0 := b0e170516 X0
           grind)
        | exact resolve b0e170516 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170516
      have b0e170526 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op x y) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e170522 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e170522
        | (have j0 := b0e170522 X0
           grind)
        | exact resolve b0e170522 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e170522
      have b0e268243 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e127
           have i₂ := b0e1853 x y
           grind)
        | exact superpose b0e1853 b0e127
        | (have j1 := b0e1853 x y
           grind)
        | exact resolve b0e127 b0e1853
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127 b0e1853
      have b0e365213 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e268243
           grind)
        | exact superpose b0e268243 b0e16
        | exact resolve b0e16 b0e268243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e268243
      have b0e366359 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e365213
           have i₂ := b0e170526 x
           grind)
        | exact superpose b0e170526 b0e365213
        | (have j1 := b0e170526 x
           grind)
        | exact resolve b0e365213 b0e170526
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170526
      have b0e366368 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e365213
           have i₂ := b0e11129 x y
           grind)
        | exact superpose b0e11129 b0e365213
        | (have j1 := b0e11129 x y
           grind)
        | exact resolve b0e365213 b0e11129
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11129 b0e365213
      have b0e366370 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by grind
      clear b0e366368
      have b0e366375 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e366370
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e366370
        | exact resolve b0e366370 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e366370
      have b0e366376 : y = (k y x) := by grind
      clear b0e366375
      have b0e366386 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e366359
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e366359
        | exact resolve b0e366359 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e366359
      have b0e366387 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e366386
      have b0e366398 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e366387
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e366387
        | exact resolve b0e366387 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e366387
      have b0e366405 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e366398
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e366398
        | exact resolve b0e366398 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e366398
      have b0e366406 : y = (M.op x y) := by grind
      clear b0e366405
      have b0e369149 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e10753
           have i₂ := b0e366406
           grind)
        | exact superpose b0e366406 b0e10753
        | exact resolve b0e10753 b0e366406
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10753
      have b0e436279 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (k y x))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e1686 x
           have i₂ := b0e1798 y x x
           grind)
        | exact superpose b0e1798 b0e1686
        | (have j1 := b0e1798 y x x
           grind)
        | exact resolve b0e1686 b0e1798
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1686 b0e1798
      have b0e437110 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e436279
           have i₂ := b0e366376
           grind)
        | exact superpose b0e366376 b0e436279
        | exact resolve b0e436279 b0e366376
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e366376 b0e436279
      have b0e437120 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e437110
           have i₂ := b0e369149
           grind)
        | exact superpose b0e369149 b0e437110
        | exact resolve b0e437110 b0e369149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e437110
      have b0e437126 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e437120
           have i₂ := b0e369149
           grind)
        | exact superpose b0e369149 b0e437120
        | exact resolve b0e437120 b0e369149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e369149 b0e437120
      have b0e451442 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e437126
           grind)
        | exact superpose b0e437126 b0e16
        | exact resolve b0e16 b0e437126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e437126
      have b0e451541 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e451442
           have i₂ := b0e366406
           grind)
        | exact superpose b0e366406 b0e451442
        | exact resolve b0e451442 b0e366406
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e451442
      have b0e451542 : (σ x) = (σ y) := by grind
      clear b0e451541
      have b0e455357 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e451542
           grind)
        | exact superpose b0e451542 b0e16
        | exact resolve b0e16 b0e451542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e455471 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e455357
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e455357
        | exact resolve b0e455357 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e455357
      have b0e455492 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e455471
           have i₂ := b0e451542
           grind)
        | exact superpose b0e451542 b0e455471
        | exact resolve b0e455471 b0e451542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e455471
      have b0e455506 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b0e455492
           have i₂ := b0e366406
           grind)
        | exact superpose b0e366406 b0e455492
        | exact resolve b0e455492 b0e366406
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e366406 b0e455492
      have b0e455510 : False := by grind
      exact b0e455510
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
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
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b1e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X1 X2 (M.op x X0)
           have i₂ := b1e10 X0 X1 x
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e47 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
      have b1e60 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e217 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e47 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47
      have b1e218 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e217
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e217
        | exact resolve b1e217 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e217
      have b1e219 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e218
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e218
        | exact resolve b1e218 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e218
      have b1e221 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b1e34 (σ x) (σ y) X0
           have i₂ := b1e219
           grind)
        | exact superpose b1e219 b1e34
        | exact resolve b1e34 b1e219
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e224 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b1e10 (σ y) X0 (σ x)
           have i₂ := b1e219
           grind)
        | exact superpose b1e219 b1e10
        | exact resolve b1e10 b1e219
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e226 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ x) (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b1e221 X0
           have i₂ := b1e10 (σ x) X0 (σ x)
           grind)
        | exact superpose b1e10 b1e221
        | exact resolve b1e221 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e221
      have b1e227 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b1e226 X0
           have i₂ := b1e224 X0
           grind)
        | exact superpose b1e224 b1e226
        | exact resolve b1e226 b1e224
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e224 b1e226
      have b1e407 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e60
      have b1e421 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e407 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e407
        | exact resolve b1e407 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e407
      have b1e2847 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e227 (σ y)
           have i₂ := b1e219
           grind)
        | exact superpose b1e219 b1e227
        | exact resolve b1e227 b1e219
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e219 b1e227
      have b1e2949 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e2847
           grind)
        | exact superpose b1e2847 b1e18
        | exact resolve b1e18 b1e2847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2951 : x = (k x (τ (σ x))) := by
        first
        | (have i₁ := b1e421 x
           have i₂ := b1e2847
           grind)
        | exact superpose b1e2847 b1e421
        | exact resolve b1e421 b1e2847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e421 b1e2847
      have b1e2984 : x = (k x x) := by
        first
        | (have i₁ := b1e2951
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e2951
        | exact resolve b1e2951 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2951
      have b1e3241 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e2984
           grind)
        | exact superpose b1e2984 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e2984
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2984
      have b1e3242 : x = (M.op x x) := by grind
      clear b1e3241
      have b1e3267 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e3242
           grind)
        | exact superpose b1e3242 b1e17
        | exact resolve b1e17 b1e3242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3242
      have b1e3391 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e2949
           have i₂ := b1e3267
           grind)
        | exact superpose b1e3267 b1e2949
        | exact resolve b1e2949 b1e3267
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2949 b1e3267
      have b1e3392 : False := by grind
      exact b1e3392
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b2e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b2e36 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 X2 (M.op x X0)
           have i₂ := b2e10 X0 X1 x
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e40 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
        intro X0
        grind
      clear b2e22
      have b2e44 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e40 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e40
        | exact resolve b2e40 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e40
      have b2e54 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e18
           have i₂ := b2e14 (σ x) X0
           grind)
        | (have i₁ := b2e18
           have i₂ := b2e14 X0 (M.op (σ x) (σ x))
           grind)
        | exact superpose b2e14 b2e18
        | (have j1 := b2e14 (σ x) X0
           grind)
        | exact resolve b2e18 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e57 : x = (M.op x y) ∨ y = (M.op x x) := by
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
      have b2e58 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e21
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e21 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e59 : (σ (M.op x y)) = (σ x) := by
        first
        | (have r₁ := b2e58
           have r₂ := b2e17
           grind)
        | exact resolve b2e58 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58
      have b2e60 : x = (M.op x y) := by
        first
        | (have r₁ := b2e57
           have r₂ := b2e17
           grind)
        | exact resolve b2e57 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e62 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b2e10 y X0 x
           have i₂ := b2e60
           grind)
        | exact superpose b2e60 b2e10
        | exact resolve b2e10 b2e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e250 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x x) X0) := by
        intro X0
        first
        | (have i₁ := b2e36 x y X0
           have i₂ := b2e60
           grind)
        | exact superpose b2e60 b2e36
        | exact resolve b2e36 b2e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36
      have b2e284 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e250 X0
           have i₂ := b2e10 x X0 x
           grind)
        | exact superpose b2e10 b2e250
        | exact resolve b2e250 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e250
      have b2e288 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b2e284 X0
           have i₂ := b2e62 X0
           grind)
        | exact superpose b2e62 b2e284
        | exact resolve b2e284 b2e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e62 b2e284
      have b2e293 : x = (M.op x x) := by
        first
        | (have i₁ := b2e288 y
           have i₂ := b2e60
           grind)
        | exact superpose b2e60 b2e288
        | exact resolve b2e288 b2e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e60 b2e288
      have b2e306 : (σ x) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e44 (σ x)
           have i₂ := b2e54 (σ (M.op (τ (σ x)) (τ (σ x))))
           grind)
        | exact superpose b2e54 b2e44
        | (have j1 := b2e54 (σ (M.op (τ (σ x)) (τ (σ x))))
           grind)
        | exact resolve b2e44 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44 b2e54
      have b2e308 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e306
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e306
        | exact resolve b2e306 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e306
      have b2e311 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e308
           have i₂ := b2e293
           grind)
        | exact superpose b2e293 b2e308
        | exact resolve b2e308 b2e293
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e308
      have b2e313 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
        first
        | (have i₁ := b2e311
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e311
        | exact resolve b2e311 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e311
      have b2e315 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e313
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e313
        | exact resolve b2e313 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e313
      have b2e317 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e315
           have i₂ := b2e293
           grind)
        | exact superpose b2e293 b2e315
        | exact resolve b2e315 b2e293
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e293 b2e315
      have b2e318 : (σ x) = (σ y) := by grind
      clear b2e317
      have b2e321 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e318
           grind)
        | exact superpose b2e318 b2e16
        | exact resolve b2e16 b2e318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e332 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b2e321
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e321
        | exact resolve b2e321 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e321
      have b2e333 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b2e332
           have i₂ := b2e318
           grind)
        | exact superpose b2e318 b2e332
        | exact resolve b2e332 b2e318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e318 b2e332
      have b2e334 : False := by grind
      exact b2e334
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e42 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
      have b3e188 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e42 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42
      have b3e189 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e188
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e188
        | exact resolve b3e188 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e188
      have b3e269 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e189
           grind)
        | exact superpose b3e189 b3e16
        | exact resolve b3e16 b3e189
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e189
      have b3e309 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e269
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e269
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e269 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e269
      have b3e310 : y = (M.op x x) := by grind
      clear b3e309
      have b3e312 : False := by grind
      exact b3e312

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4423 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4423 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
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
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e35 X0 x
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e35
        | exact resolve b0e35 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e42 : (σ y) = (k (σ y) (M.op y (σ y))) := by grind
      have b0e57 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (M.op X3 X0) = (k X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X3
           have i₂ := b0e14 X3 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X2 X2)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X3 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e59 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X1 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X0 X1)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 : G, (M.op y (σ y)) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e38 (σ y)
           have i₂ := b0e14 (σ y) X0
           grind)
        | (have i₁ := b0e38 X0
           have i₂ := b0e14 X0 (M.op (σ y) X0)
           grind)
        | exact superpose b0e14 b0e38
        | (have j1 := b0e14 (σ y) X0
           grind)
        | exact resolve b0e38 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b0e65 : ∀ X0 : G, (M.op y X0) = (k (σ y) X0) ∨ (M.op y (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e61 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e61
        | (have j0 := b0e61 X0
           grind)
        | exact resolve b0e61 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e66 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y X1) ∨ (M.op X3 X0) = (k X3 X0) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e57 X0 X1 x X3
           have i₂ := b0e36 X1 x
           grind)
        | exact superpose b0e36 b0e57
        | (have j0 := b0e57 X0 X1 x X3
           grind)
        | exact resolve b0e57 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e68 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e36 X0 (M.op X0 x)
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e36
        | exact resolve b0e36 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e72 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e36 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e36
        | exact resolve b0e36 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e74 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e36 x x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e36
        | exact resolve b0e36 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e78 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X0 (M.op y X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 X0 (M.op X0 x) X2
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 : G, (M.op y (σ y)) = (M.op y (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 (M.op (σ y) X0)
           have i₂ := b0e36 (σ y) X0
           grind)
        | exact superpose b0e36 b0e38
        | exact resolve b0e38 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : ∀ X0 : G, (M.op y (σ y)) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e79 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e79
        | exact resolve b0e79 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e85 : (M.op y (σ y)) = (M.op y y) := by
        first
        | (have i₁ := b0e80 x
           have i₂ := b0e36 y x
           grind)
        | exact superpose b0e36 b0e80
        | exact resolve b0e80 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e96 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e370 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e68 (M.op y x)
           have i₂ := b0e36 y x
           grind)
        | exact superpose b0e36 b0e68
        | exact resolve b0e68 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e533 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e58 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e802 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ (σ y) = (M.op y (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e66 (σ x) (σ x) X0
           grind)
        | exact superpose b0e66 b0e18
        | (have j1 := b0e66 (σ x) x X0
           grind)
        | exact resolve b0e18 b0e66
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1217 : (σ y) = (k (σ y) (M.op y y)) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e85
           grind)
        | exact superpose b0e85 b0e42
        | exact resolve b0e42 b0e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e1312 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) y) ∨ (M.op X3 X1) = (k X3 X1) ∨ (M.op y X2) = (k y X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e66 X1 X2 X3
           have i₂ := b0e59 X2 y X0
           grind)
        | exact superpose b0e59 b0e66
        | (have j0 := b0e66 X1 X1 X3
           have j1 := b0e59 X1 X3 X2
           grind)
        | exact resolve b0e66 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e1387 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op y (M.op y y)) ∨ (M.op X3 X1) = (k X3 X1) ∨ (M.op y X2) = (k y X2) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e1312 x X1 X2 X3
           have i₂ := b0e78 y x
           grind)
        | exact superpose b0e78 b0e1312
        | (have j0 := b0e1312 x X1 X2 X3
           grind)
        | exact resolve b0e1312 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1312
      have b0e1473 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op y y) ∨ (M.op X3 X1) = (k X3 X1) ∨ (M.op y X2) = (k y X2) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e1387 X1 X2 X3
           have i₂ := b0e36 y y
           grind)
        | exact superpose b0e36 b0e1387
        | (have j0 := b0e1387 X1 X2 X3
           grind)
        | exact resolve b0e1387 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1387
      have b0e1745 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e62 X0 X0
           have i₂ := b0e14 (σ X0) X1
           grind)
        | (have i₁ := b0e62 X0 X1
           have i₂ := b0e14 X0 (M.op (σ X0) (σ X1))
           grind)
        | exact superpose b0e14 b0e62
        | (have j1 := b0e14 (σ X1) X0
           grind)
        | exact resolve b0e62 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1794 : ∀ X0 : G, (σ X0) = (M.op y (σ y)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 (σ y)
           have i₂ := b0e62 y X0
           grind)
        | exact superpose b0e62 b0e38
        | (have j1 := b0e62 y X0
           grind)
        | exact resolve b0e38 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e1828 : ∀ X0 : G, (σ X0) = (M.op y y) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e1794 X0
           have i₂ := b0e85
           grind)
        | exact superpose b0e85 b0e1794
        | (have j0 := b0e1794 X0
           grind)
        | exact resolve b0e1794 b0e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1794
      have b0e1858 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e1828 X0
           have i₂ := b0e38 (σ X0)
           grind)
        | exact superpose b0e38 b0e1828
        | (have j0 := b0e1828 X0
           grind)
        | exact resolve b0e1828 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1828
      have b0e1939 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e72
           grind)
        | exact superpose b0e72 b0e16
        | exact resolve b0e16 b0e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72
      have b0e1958 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e96
      have b0e1977 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1958 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e1958
        | exact resolve b0e1958 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1958
      have b0e2002 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e533 X0 (M.op X0 X1)
           have i₂ := b0e36 X0 X1
           grind)
        | exact superpose b0e36 b0e533
        | (have j0 := b0e533 X0 (M.op X0 X1)
           grind)
        | exact resolve b0e533 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2029 : y ≠ (M.op y y) ∨ y = (k y (σ y)) := by
        first
        | (have i₁ := b0e533 y (σ y)
           have i₂ := b0e85
           grind)
        | exact superpose b0e85 b0e533
        | (have j0 := b0e533 y y
           grind)
        | exact resolve b0e533 b0e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2442 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ (σ y)) X0) ∨ (τ X0) = (M.op y (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e24 X0 (σ y)
           have i₂ := b0e65 (τ X0)
           grind)
        | exact superpose b0e65 b0e24
        | (have j1 := b0e65 (τ X0)
           grind)
        | exact resolve b0e24 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e65
      have b0e2445 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k (σ (σ y)) X0) ∨ (τ X0) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e2442 X0
           have i₂ := b0e85
           grind)
        | exact superpose b0e85 b0e2442
        | (have j0 := b0e2442 X0
           grind)
        | exact resolve b0e2442 b0e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85 b0e2442
      have b0e2791 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) y) ≠ X1 ∨ (k X1 (M.op X1 X2)) = X1 ∨ (M.op y X1) = (k y X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e2002 X1 X2
           have i₂ := b0e59 X1 y X0
           grind)
        | exact superpose b0e59 b0e2002
        | (have j0 := b0e2002 X1 X2
           have j1 := b0e59 X1 y X2
           grind)
        | (have r₁ := b0e2002 (M.op (M.op X2 X2) y) X1
           have r₂ := b0e59 (M.op (M.op X2 X2) y) y X2
           grind)
        | exact resolve b0e2002 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e2002
      have b0e2793 : ∀ X1 X2 : G, (M.op y (M.op y y)) ≠ X1 ∨ (k X1 (M.op X1 X2)) = X1 ∨ (M.op y X1) = (k y X1) := by
        intro X1 X2
        first
        | (have i₁ := b0e2791 x X1 X2
           have i₂ := b0e78 y x
           grind)
        | exact superpose b0e78 b0e2791
        | (have j0 := b0e2791 x X1 X2
           grind)
        | (have r₁ := b0e2791 X2 (M.op y (M.op y y)) X2
           have r₂ := b0e78 y X2
           grind)
        | exact resolve b0e2791 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78 b0e2791
      have b0e2801 : ∀ X1 X2 : G, (M.op y y) ≠ X1 ∨ (k X1 (M.op X1 X2)) = X1 ∨ (M.op y X1) = (k y X1) := by
        intro X1 X2
        first
        | (have i₁ := b0e2793 X1 X2
           have i₂ := b0e36 y y
           grind)
        | exact superpose b0e36 b0e2793
        | (have j0 := b0e2793 X1 X2
           grind)
        | (have r₁ := b0e2793 (M.op y y) X2
           have r₂ := b0e36 y y
           grind)
        | (have r₁ := b0e2793 (M.op (M.op y y) (M.op (M.op y y) X1)) X2
           have r₂ := b0e36 (M.op y y) X1
           grind)
        | exact resolve b0e2793 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2793
      have b0e2804 : ∀ X1 X2 : G, (k X1 (M.op X1 X2)) = X1 ∨ (M.op y X1) = (k y X1) := by
        intro X1 X2
        first
        | (have j0 := b0e2801 X1 X2
           have j1 := b0e14 y X1
           grind)
        | (have r₁ := b0e2801 X1 X2
           have r₂ := b0e14 y X1
           grind)
        | (have r₁ := b0e2801 (M.op x x) X2
           have r₂ := b0e14 x (M.op y y)
           grind)
        | (have r₁ := b0e2801 (k y y) X2
           have r₂ := b0e14 y y
           grind)
        | exact resolve b0e2801 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2801
      have b0e9475 : (σ y) = (M.op (σ y) (M.op y y)) ∨ (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y y) := by
        first
        | (have i₁ := b0e1217
           have i₂ := b0e1745 (M.op y y) y
           grind)
        | exact superpose b0e1745 b0e1217
        | (have j1 := b0e1745 (M.op y y) y
           grind)
        | exact resolve b0e1217 b0e1745
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1217 b0e1745
      have b0e9545 : (σ y) = (M.op y (M.op y y)) ∨ (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y y) := by
        first
        | (have i₁ := b0e9475
           have i₂ := b0e38 (M.op y y)
           grind)
        | exact superpose b0e38 b0e9475
        | exact resolve b0e9475 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9475
      have b0e9574 : (σ y) = (M.op y y) ∨ (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y y) := by
        first
        | (have i₁ := b0e9545
           have i₂ := b0e36 y y
           grind)
        | exact superpose b0e36 b0e9545
        | exact resolve b0e9545 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e9545
      have b0e9575 : (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y y) := by grind
      clear b0e9574
      have b0e16011 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y y) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e1473 X0 X0 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1473
      have b0e16012 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e16011 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16011
      have b0e18135 : ∀ X0 : G, y = (k y (M.op X0 X0)) ∨ (M.op y X0) = (k y X0) := by
        intro X0
        grind
      clear b0e16012
      have b0e37349 : y = (k y y) ∨ (M.op y x) = (k y x) := by
        first
        | (have i₁ := b0e18135 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e18135
        | (have j0 := b0e18135 x
           grind)
        | exact resolve b0e18135 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18135
      have b0e37453 : y = (k y y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e37349
           have i₂ := b0e74
           grind)
        | exact superpose b0e74 b0e37349
        | exact resolve b0e37349 b0e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37349
      have b0e39024 : y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e14 y y
           have i₂ := b0e37453
           grind)
        | exact superpose b0e37453 b0e14
        | (have j0 := b0e14 y y
           grind)
        | exact resolve b0e14 b0e37453
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37453
      have b0e39042 : (M.op x y) = (k y x) ∨ y = (M.op y y) := by grind
      clear b0e39024
      have b0e39426 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e1858 x
           have i₂ := b0e39042
           grind)
        | exact superpose b0e39042 b0e1858
        | (have j0 := b0e1858 x
           grind)
        | exact resolve b0e1858 b0e39042
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1858 b0e39042
      have b0e39460 : (σ x) = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b0e39426
           have r₂ := b0e1939
           grind)
        | exact resolve b0e39426 b0e1939
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39426
      have b0e39834 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e370 y
           have i₂ := b0e39460
           grind)
        | exact superpose b0e39460 b0e370
        | exact resolve b0e370 b0e39460
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e370
      have b0e39881 : y ≠ (σ x) ∨ y = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e533 y y
           have i₂ := b0e39460
           grind)
        | exact superpose b0e39460 b0e533
        | (have j0 := b0e533 y y
           grind)
        | (have r₁ := b0e533 y y
           have r₂ := b0e39460
           grind)
        | exact resolve b0e533 b0e39460
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39460
      have b0e39888 : y ≠ (σ x) ∨ y = (k y y) := by
        first
        | (have j1 := b0e533 y y
           grind)
        | (have r₁ := b0e39881
           have r₂ := b0e533 y y
           grind)
        | exact resolve b0e39881 b0e533
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39881
      have b0e39903 : y = (M.op y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e39834
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e39834
        | exact resolve b0e39834 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39834
      have b0e40693 : y ≠ y ∨ y = (k y (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e2029
           have i₂ := b0e39903
           grind)
        | exact superpose b0e39903 b0e2029
        | (have r₁ := b0e2029
           have r₂ := b0e39903
           grind)
        | exact resolve b0e2029 b0e39903
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2029
      have b0e40752 : y = (k y y) ∨ y = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e2804 y y
           have i₂ := b0e39903
           grind)
        | exact superpose b0e39903 b0e2804
        | exact resolve b0e2804 b0e39903
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2804
      have b0e40753 : y = (k y y) ∨ (σ x) = (σ y) := by grind
      clear b0e40752
      have b0e40759 : y = (k y (σ y)) ∨ (σ x) = (σ y) := by grind
      clear b0e40693
      have b0e41593 : (σ y) = (M.op y y) ∨ (σ y) = (M.op y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e9575
           have i₂ := b0e40753
           grind)
        | exact superpose b0e40753 b0e9575
        | exact resolve b0e9575 b0e40753
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40753
      have b0e41634 : (σ y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
      clear b0e41593
      have b0e44093 : y = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e39903
           have i₂ := b0e41634
           grind)
        | exact superpose b0e41634 b0e39903
        | exact resolve b0e39903 b0e41634
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39903 b0e41634
      have b0e44151 : (σ x) = (σ y) ∨ y = (σ y) := by grind
      clear b0e44093
      have b0e44812 : y = (k y (τ (M.op (σ x) (σ x)))) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e1977 y
           have i₂ := b0e44151
           grind)
        | exact superpose b0e44151 b0e1977
        | exact resolve b0e1977 b0e44151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1977 b0e44151
      have b0e44817 : y = (k y (τ (σ y))) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e44812
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e44812
        | exact resolve b0e44812 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44812
      have b0e44857 : y = (k y y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e44817
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e44817
        | exact resolve b0e44817 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44817
      have b0e48164 : (σ y) = (M.op y y) ∨ (σ y) = (M.op y y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e9575
           have i₂ := b0e44857
           grind)
        | exact superpose b0e44857 b0e9575
        | exact resolve b0e9575 b0e44857
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9575
      have b0e48184 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e14 y y
           have i₂ := b0e44857
           grind)
        | exact superpose b0e44857 b0e14
        | (have j0 := b0e14 y y
           grind)
        | exact resolve b0e14 b0e44857
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44857
      have b0e48202 : y = (M.op y y) ∨ y = (σ y) := by grind
      clear b0e48184
      have b0e48209 : (σ y) = (M.op y y) ∨ y = (σ y) := by grind
      clear b0e48164
      have b0e50705 : y = (σ y) ∨ y = (σ y) ∨ y = (σ y) := by
        first
        | (have i₁ := b0e48202
           have i₂ := b0e48209
           grind)
        | exact superpose b0e48209 b0e48202
        | exact resolve b0e48202 b0e48209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48202 b0e48209
      have b0e50771 : y = (σ y) := by grind
      clear b0e50705
      have b0e51138 : y = (k y y) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e40759
           have i₂ := b0e50771
           grind)
        | exact superpose b0e50771 b0e40759
        | exact resolve b0e40759 b0e50771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40759
      have b0e51140 : y = (τ y) := by
        first
        | (have i₁ := b0e11 y
           have i₂ := b0e50771
           grind)
        | exact superpose b0e50771 b0e11
        | exact resolve b0e11 b0e50771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51141 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 y X0
           have i₂ := b0e50771
           grind)
        | exact superpose b0e50771 b0e15
        | exact resolve b0e15 b0e50771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51222 : y = (k y y) := by
        first
        | (have r₁ := b0e51138
           have r₂ := b0e39888
           grind)
        | exact resolve b0e51138 b0e39888
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39888 b0e51138
      have b0e52435 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e14 y y
           have i₂ := b0e51222
           grind)
        | exact superpose b0e51222 b0e14
        | (have j0 := b0e14 y y
           grind)
        | exact resolve b0e14 b0e51222
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51222
      have b0e52453 : y = (M.op y y) := by grind
      clear b0e52435
      have b0e66273 : (M.op (σ (σ y)) (σ x)) = (σ (M.op y (τ (σ x)))) ∨ (σ y) = (M.op y (σ x)) ∨ (M.op y y) = (τ (σ x)) := by
        first
        | (have i₁ := b0e802 (σ (σ y))
           have i₂ := b0e2445 (σ x)
           grind)
        | exact superpose b0e2445 b0e802
        | (have j1 := b0e2445 (σ x)
           grind)
        | exact resolve b0e802 b0e2445
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e802 b0e2445
      have b0e66320 : (σ (M.op y x)) = (M.op (σ (σ y)) (σ x)) ∨ (σ y) = (M.op y (σ x)) ∨ (M.op y y) = (τ (σ x)) := by
        first
        | (have i₁ := b0e66273
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e66273
        | exact resolve b0e66273 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66273
      have b0e66536 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (M.op y (σ x)) ∨ (M.op y y) = (τ (σ x)) := by
        first
        | (have i₁ := b0e66320
           have i₂ := b0e50771
           grind)
        | exact superpose b0e50771 b0e66320
        | exact resolve b0e66320 b0e50771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66320
      have b0e66749 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op y (σ x)) ∨ (M.op y y) = (τ (σ x)) := by
        first
        | (have i₁ := b0e66536
           have i₂ := b0e74
           grind)
        | exact superpose b0e74 b0e66536
        | exact resolve b0e66536 b0e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66536
      have b0e66939 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ y) = (M.op y (σ x)) ∨ (M.op y y) = (τ (σ x)) := by
        first
        | (have i₁ := b0e66749
           have i₂ := b0e38 (σ x)
           grind)
        | exact superpose b0e38 b0e66749
        | exact resolve b0e66749 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e66749
      have b0e67088 : (σ y) = (M.op y (σ x)) ∨ (M.op y y) = (τ (σ x)) := by
        first
        | (have r₁ := b0e66939
           have r₂ := b0e1939
           grind)
        | exact resolve b0e66939 b0e1939
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66939
      have b0e67203 : y = (M.op y (σ x)) ∨ (M.op y y) = (τ (σ x)) := by
        first
        | (have i₁ := b0e67088
           have i₂ := b0e50771
           grind)
        | exact superpose b0e50771 b0e67088
        | exact resolve b0e67088 b0e50771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67088
      have b0e67280 : x = (M.op y y) ∨ y = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e67203
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e67203
        | exact resolve b0e67203 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67203
      have b0e67334 : y = (M.op y (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e67280
           have i₂ := b0e52453
           grind)
        | exact superpose b0e52453 b0e67280
        | exact resolve b0e67280 b0e52453
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67280
      have b0e68534 : y ≠ y ∨ y = (k y (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e533 y (σ x)
           have i₂ := b0e67334
           grind)
        | exact superpose b0e67334 b0e533
        | (have j0 := b0e533 y (σ x)
           grind)
        | (have r₁ := b0e533 y (σ x)
           have r₂ := b0e67334
           grind)
        | exact resolve b0e533 b0e67334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e533
      have b0e68545 : y = (k y (σ x)) ∨ x = y := by grind
      clear b0e68534
      have b0e68549 : y = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e68545
           have i₂ := b0e51141 x
           grind)
        | exact superpose b0e51141 b0e68545
        | exact resolve b0e68545 b0e51141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51141 b0e68545
      have b0e69308 : (k y x) = (τ y) ∨ x = y := by
        first
        | (have i₁ := b0e11 (k y x)
           have i₂ := b0e68549
           grind)
        | exact superpose b0e68549 b0e11
        | exact resolve b0e11 b0e68549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68549
      have b0e69446 : y = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e69308
           have i₂ := b0e51140
           grind)
        | exact superpose b0e51140 b0e69308
        | exact resolve b0e69308 b0e51140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51140 b0e69308
      have b0e69971 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e69446
           grind)
        | exact superpose b0e69446 b0e14
        | (have j0 := b0e14 y x
           grind)
        | exact resolve b0e14 b0e69446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69446
      have b0e70017 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e69971
           have i₂ := b0e74
           grind)
        | exact superpose b0e74 b0e69971
        | exact resolve b0e69971 b0e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74 b0e69971
      have b0e70070 : x = y ∨ y = (M.op x y) ∨ x = y := by
        first
        | (have i₁ := b0e70017
           have i₂ := b0e52453
           grind)
        | exact superpose b0e52453 b0e70017
        | exact resolve b0e70017 b0e52453
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52453 b0e70017
      have b0e70071 : y = (M.op x y) ∨ x = y := by grind
      clear b0e70070
      have b0e70667 : (σ y) ≠ (M.op y (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e1939
           have i₂ := b0e70071
           grind)
        | exact superpose b0e70071 b0e1939
        | exact resolve b0e1939 b0e70071
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1939 b0e70071
      have b0e70698 : y ≠ (M.op y (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e70667
           have i₂ := b0e50771
           grind)
        | exact superpose b0e50771 b0e70667
        | exact resolve b0e70667 b0e50771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50771 b0e70667
      have b0e70701 : x = y := by
        first
        | (have r₁ := b0e70698
           have r₂ := b0e67334
           grind)
        | exact resolve b0e70698 b0e67334
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67334 b0e70698
      have b0e71376 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e70701
           grind)
        | exact superpose b0e70701 b0e16
        | exact resolve b0e16 b0e70701
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70701
      have b0e71578 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e71376
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e71376
        | exact resolve b0e71376 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71376
      have b0e71620 : False := by grind
      exact b0e71620
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
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
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b1e32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e50 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e53 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
      have b1e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b1e66 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e420 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e50 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e591 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e53 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53
      have b1e592 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e591
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e591
        | exact resolve b1e591 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e591
      have b1e593 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e592
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e592
        | exact resolve b1e592 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e592
      have b1e594 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e593
           grind)
        | exact superpose b1e593 b1e16
        | exact resolve b1e16 b1e593
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e597 : (M.op (σ x) (σ x)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e32 (σ x) (σ y)
           have i₂ := b1e593
           grind)
        | exact superpose b1e593 b1e32
        | exact resolve b1e32 b1e593
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32 b1e593
      have b1e1059 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e66
      have b1e1076 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1059 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e1059
        | exact resolve b1e1059 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1059
      have b1e1104 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e54 x x
           grind)
        | exact superpose b1e54 b1e18
        | (have j1 := b1e54 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e54 x y
           grind)
        | exact resolve b1e18 b1e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e1177 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e1104
           have i₂ := b1e597
           grind)
        | exact superpose b1e597 b1e1104
        | exact resolve b1e1104 b1e597
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1104
      have b1e1213 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e420 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e420
        | (have j0 := b1e420 x x
           grind)
        | exact resolve b1e420 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e420
      have b1e1618 : x = (k x (τ (M.op y (σ x)))) := by
        first
        | (have i₁ := b1e1076 x
           have i₂ := b1e597
           grind)
        | exact superpose b1e597 b1e1076
        | exact resolve b1e1076 b1e597
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e597 b1e1076
      have b1e1651 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1177
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e1177
        | (have j1 := b1e14 x x
           grind)
        | exact resolve b1e1177 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1177
      have b1e1667 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1651
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1651
        | exact resolve b1e1651 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1651
      have b1e1668 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by grind
      clear b1e1667
      have b1e1669 : (σ x) = (M.op y (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e1668
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1668
        | exact resolve b1e1668 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1668
      have b1e1776 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e1618
           have i₂ := b1e1669
           grind)
        | exact superpose b1e1669 b1e1618
        | exact resolve b1e1618 b1e1669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1618 b1e1669
      have b1e1795 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e1776
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e1776
        | exact resolve b1e1776 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1776
      have b1e1798 : x = (k x x) := by
        first
        | (have r₁ := b1e1795
           have r₂ := b1e1213
           grind)
        | exact resolve b1e1795 b1e1213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1213 b1e1795
      have b1e1861 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e1798
           grind)
        | exact superpose b1e1798 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e1798
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1798
      have b1e1866 : x = (M.op x x) := by grind
      clear b1e1861
      have b1e1937 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e1866
           grind)
        | exact superpose b1e1866 b1e17
        | exact resolve b1e17 b1e1866
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1866
      have b1e2029 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e594
           have i₂ := b1e1937
           grind)
        | exact superpose b1e1937 b1e594
        | exact resolve b1e594 b1e1937
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e594
      have b1e2036 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e2029
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e2029
        | exact resolve b1e2029 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2029
      have b1e2042 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e2036
           have i₂ := b1e1937
           grind)
        | exact superpose b1e1937 b1e2036
        | exact resolve b1e2036 b1e1937
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1937 b1e2036
      have b1e2043 : False := by grind
      exact b1e2043
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b2e48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b2e53 : x = (M.op x y) ∨ y = (M.op x x) := by
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
      have b2e56 : x = (M.op x y) := by
        first
        | (have r₁ := b2e53
           have r₂ := b2e17
           grind)
        | exact resolve b2e53 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53
      have b2e1826 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e51 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e51
        | exact resolve b2e51 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e2023 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e1826
           grind)
        | exact superpose b2e1826 b2e11
        | exact resolve b2e11 b2e1826
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1826
      have b2e2036 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e2023
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e2023
        | exact resolve b2e2023 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2023
      have b2e2043 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e48 x x
           have i₂ := b2e2036
           grind)
        | exact superpose b2e2036 b2e48
        | exact resolve b2e48 b2e2036
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48 b2e2036
      have b2e2046 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e2043
           have r₂ := b2e17
           grind)
        | exact resolve b2e2043 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2043
      have b2e2118 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e2046
           grind)
        | exact superpose b2e2046 b2e11
        | exact resolve b2e11 b2e2046
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2046
      have b2e2134 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e2118
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e2118
        | exact resolve b2e2118 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2118
      have b2e2135 : x = y := by grind
      clear b2e2134
      have b2e2171 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e2135
           grind)
        | exact superpose b2e2135 b2e16
        | exact resolve b2e16 b2e2135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2176 : x = (M.op x x) := by
        first
        | (have i₁ := b2e56
           have i₂ := b2e2135
           grind)
        | exact superpose b2e2135 b2e56
        | exact resolve b2e56 b2e2135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56
      have b2e2189 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e2171
           have i₂ := b2e2176
           grind)
        | exact superpose b2e2176 b2e2171
        | exact resolve b2e2171 b2e2176
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2171 b2e2176
      have b2e2194 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e2189
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e2189
        | exact resolve b2e2189 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2189
      have b2e2196 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e2194
           have i₂ := b2e2135
           grind)
        | exact superpose b2e2135 b2e2194
        | exact resolve b2e2194 b2e2135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2135 b2e2194
      have b2e2197 : False := by grind
      exact b2e2197
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x x) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e37 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
      have b3e212 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e37 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37
      have b3e213 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e212
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e212
        | exact resolve b3e212 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e212
      have b3e214 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e213
           grind)
        | exact superpose b3e213 b3e16
        | exact resolve b3e16 b3e213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e213
      have b3e275 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b3e214
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e214
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e214 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e214
      have b3e276 : y = (M.op x x) := by grind
      clear b3e275
      have b3e278 : False := by grind
      exact b3e278

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4423 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4423 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e35 X0 x
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e35
        | exact resolve b0e35 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e57 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X3
           have i₂ := b0e14 X3 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X2 X2)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X3 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e59 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X1 X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X0 X1)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X1 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b0e65 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y X1) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e57 X0 X1 x X3
           have i₂ := b0e36 X1 x
           grind)
        | exact superpose b0e36 b0e57
        | (have j0 := b0e57 X0 X1 x X3
           grind)
        | exact resolve b0e57 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e66 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e36 X0 (M.op X0 x)
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e36
        | exact resolve b0e36 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e36 (σ x) (σ x)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e36
        | exact resolve b0e36 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X0 (M.op y X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 X0 (M.op X0 x) X2
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 : G, (M.op y (σ y)) = (M.op y (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 (M.op (σ y) X0)
           have i₂ := b0e36 (σ y) X0
           grind)
        | exact superpose b0e36 b0e38
        | exact resolve b0e38 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e78 : ∀ X0 : G, (M.op y (σ y)) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e77 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e77
        | exact resolve b0e77 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e83 : (M.op y (σ y)) = (M.op y y) := by
        first
        | (have i₁ := b0e78 x
           have i₂ := b0e36 y x
           grind)
        | exact superpose b0e36 b0e78
        | exact resolve b0e78 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e364 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e66 (M.op y x)
           have i₂ := b0e36 y x
           grind)
        | exact superpose b0e36 b0e66
        | exact resolve b0e66 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e525 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e58 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e1302 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) y) ∨ (M.op X1 X3) = (k X3 X1) ∨ (M.op X2 y) = (k y X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e65 X1 X2 X3
           have i₂ := b0e59 X2 y X0
           grind)
        | exact superpose b0e59 b0e65
        | (have j0 := b0e65 X1 X1 X3
           have j1 := b0e59 X1 X3 X2
           grind)
        | exact resolve b0e65 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e65
      have b0e1378 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op y (M.op y y)) ∨ (M.op X1 X3) = (k X3 X1) ∨ (M.op X2 y) = (k y X2) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e1302 x X1 X2 X3
           have i₂ := b0e76 y x
           grind)
        | exact superpose b0e76 b0e1302
        | (have j0 := b0e1302 x X1 X2 X3
           grind)
        | exact resolve b0e1302 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76 b0e1302
      have b0e1462 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op y y) ∨ (M.op X1 X3) = (k X3 X1) ∨ (M.op X2 y) = (k y X2) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e1378 X1 X2 X3
           have i₂ := b0e36 y y
           grind)
        | exact superpose b0e36 b0e1378
        | (have j0 := b0e1378 X1 X2 X3
           grind)
        | exact resolve b0e1378 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e1378
      have b0e1746 : ∀ X0 : G, (σ X0) = (M.op y (σ y)) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e38 (σ y)
           have i₂ := b0e62 X0 y
           grind)
        | exact superpose b0e62 b0e38
        | (have j1 := b0e62 X0 y
           grind)
        | exact resolve b0e38 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e62
      have b0e1780 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e1746 X0
           have i₂ := b0e83
           grind)
        | exact superpose b0e83 b0e1746
        | (have j0 := b0e1746 X0
           grind)
        | exact resolve b0e1746 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83 b0e1746
      have b0e1888 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e70
           grind)
        | exact superpose b0e70 b0e16
        | exact resolve b0e16 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e4848 : (M.op y (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op y y) := by
        first
        | (have i₁ := b0e70
           have i₂ := b0e1780 x
           grind)
        | exact superpose b0e1780 b0e70
        | (have j1 := b0e1780 x
           grind)
        | exact resolve b0e70 b0e1780
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70 b0e1780
      have b0e15587 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op y y) ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e1462 X0 X0 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1462
      have b0e15588 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e15587 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15587
      have b0e21752 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e525 X0 X0
           have i₂ := b0e15588 X0
           grind)
        | (have i₁ := b0e525 y y
           have i₂ := b0e15588 X0
           grind)
        | exact superpose b0e15588 b0e525
        | (have j0 := b0e525 X0 X0
           have j1 := b0e15588 X0
           grind)
        | (have r₁ := b0e525 (M.op y y) (M.op y y)
           have r₂ := b0e15588 (M.op y y)
           grind)
        | exact resolve b0e525 b0e15588
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e525 b0e15588
      have b0e21917 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e21752 X0
           have j1 := b0e14 y X0
           grind)
        | (have r₁ := b0e21752 x
           have r₂ := b0e14 y x
           grind)
        | (have r₁ := b0e21752 (M.op X0 X0)
           have r₂ := b0e14 X0 (M.op y y)
           grind)
        | (have r₁ := b0e21752 (k y y)
           have r₂ := b0e14 y y
           grind)
        | exact resolve b0e21752 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21752
      have b0e22607 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e21917 X0
           grind)
        | exact superpose b0e21917 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e21917 X0
           grind)
        | exact resolve b0e14 b0e21917
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21917
      have b0e22680 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e22607 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22607
      have b0e43365 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e4848
           have i₂ := b0e22680 x
           grind)
        | exact superpose b0e22680 b0e4848
        | (have j1 := b0e22680 x
           grind)
        | exact resolve b0e4848 b0e22680
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4848 b0e22680
      have b0e43536 : (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have r₁ := b0e43365
           have r₂ := b0e1888
           grind)
        | exact resolve b0e43365 b0e1888
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1888 b0e43365
      have b0e43548 : (σ x) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e43536
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e43536
        | exact resolve b0e43536 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43536
      have b0e43573 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e364 y
           have i₂ := b0e43548
           grind)
        | exact superpose b0e43548 b0e364
        | exact resolve b0e364 b0e43548
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e364 b0e43548
      have b0e43639 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e43573
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e43573
        | exact resolve b0e43573 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43573
      have b0e43744 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e11 y
           have i₂ := b0e43639
           grind)
        | exact superpose b0e43639 b0e11
        | exact resolve b0e11 b0e43639
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43639
      have b0e43872 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e43744
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e43744
        | exact resolve b0e43744 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43744
      have b0e43873 : x = y := by grind
      clear b0e43872
      have b0e44813 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e43873
           grind)
        | exact superpose b0e43873 b0e16
        | exact resolve b0e16 b0e43873
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43873
      have b0e44964 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e44813
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e44813
        | exact resolve b0e44813 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44813
      have b0e45014 : False := by grind
      exact b0e45014
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
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
      have b1e32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e40 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op y X0) := by
        intro X0 X2
        first
        | (have i₁ := b1e10 X0 x X2
           have i₂ := b1e32 X0 x
           grind)
        | exact superpose b1e32 b1e10
        | exact resolve b1e10 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e53 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
      have b1e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b1e66 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e414 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e50 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e586 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b1e53 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e53
      have b1e587 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e586
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e586
        | exact resolve b1e586 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e586
      have b1e588 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e587
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e587
        | exact resolve b1e587 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e587
      have b1e591 : (M.op (σ y) (σ x)) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e32 (σ y) (σ x)
           have i₂ := b1e588
           grind)
        | exact superpose b1e588 b1e32
        | exact resolve b1e32 b1e588
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e594 : (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e591
           have i₂ := b1e588
           grind)
        | exact superpose b1e588 b1e591
        | exact resolve b1e591 b1e588
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e588 b1e591
      have b1e717 : (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e32 y (σ y)
           have i₂ := b1e594
           grind)
        | exact superpose b1e594 b1e32
        | exact resolve b1e32 b1e594
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32
      have b1e1102 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e54 x x
           grind)
        | exact superpose b1e54 b1e18
        | (have j1 := b1e54 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e54 y x
           grind)
        | exact resolve b1e18 b1e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e1193 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b1e66
      have b1e1210 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e1193 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e1193
        | exact resolve b1e1193 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1193
      have b1e1232 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e414 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e414
        | (have j0 := b1e414 x x
           grind)
        | exact resolve b1e414 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e414
      have b1e1992 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1102
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e1102
        | (have j1 := b1e14 (σ x) (σ x)
           grind)
        | exact resolve b1e1102 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1102
      have b1e2008 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e1992
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1992
        | exact resolve b1e1992 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1992
      have b1e2009 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
      clear b1e2008
      have b1e2012 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
        first
        | (have i₁ := b1e2009
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e2009
        | exact resolve b1e2009 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2009
      have b1e2018 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e1210 x
           have i₂ := b1e2012
           grind)
        | exact superpose b1e2012 b1e1210
        | exact resolve b1e1210 b1e2012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1210 b1e2012
      have b1e2056 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e2018
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e2018
        | exact resolve b1e2018 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2018
      have b1e2061 : x = (k x x) := by
        first
        | (have r₁ := b1e2056
           have r₂ := b1e1232
           grind)
        | exact resolve b1e2056 b1e1232
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1232 b1e2056
      have b1e2081 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e2061
           grind)
        | exact superpose b1e2061 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e2061
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2061
      have b1e2086 : x = (M.op x x) := by grind
      clear b1e2081
      have b1e2118 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e2086
           grind)
        | exact superpose b1e2086 b1e17
        | exact resolve b1e17 b1e2086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2126 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b1e40 X0 x
           have i₂ := b1e2086
           grind)
        | exact superpose b1e2086 b1e40
        | exact resolve b1e40 b1e2086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40 b1e2086
      have b1e2368 : (σ x) = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e594
           have i₂ := b1e2118
           grind)
        | exact superpose b1e2118 b1e594
        | exact resolve b1e594 b1e2118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e594
      have b1e3251 : (M.op y y) = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e717
           have i₂ := b1e2126 (σ x)
           grind)
        | exact superpose b1e2126 b1e717
        | exact resolve b1e717 b1e2126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e717
      have b1e3318 : (σ x) = (M.op y y) := by
        first
        | (have i₁ := b1e3251
           have i₂ := b1e2368
           grind)
        | exact superpose b1e2368 b1e3251
        | exact resolve b1e3251 b1e2368
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2368 b1e3251
      have b1e3364 : (M.op x y) = (σ x) := by
        first
        | (have i₁ := b1e3318
           have i₂ := b1e2126 y
           grind)
        | exact superpose b1e2126 b1e3318
        | exact resolve b1e3318 b1e2126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2126 b1e3318
      have b1e3404 : (σ x) = (M.op x x) := by
        first
        | (have i₁ := b1e3364
           have i₂ := b1e2118
           grind)
        | exact superpose b1e2118 b1e3364
        | exact resolve b1e3364 b1e2118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3364
      have b1e3429 : y = (σ x) := by
        first
        | (have i₁ := b1e3404
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e3404
        | exact resolve b1e3404 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3404
      have b1e3443 : x = (σ x) := by
        first
        | (have i₁ := b1e3429
           have i₂ := b1e2118
           grind)
        | exact superpose b1e2118 b1e3429
        | exact resolve b1e3429 b1e2118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3429
      have b1e3790 : (σ y) ≠ (M.op x x) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e3443
           grind)
        | exact superpose b1e3443 b1e18
        | exact resolve b1e18 b1e3443
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e3822 : y ≠ (σ y) := by
        first
        | (have i₁ := b1e3790
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e3790
        | exact resolve b1e3790 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3790
      have b1e3828 : x ≠ (σ x) := by
        first
        | (have i₁ := b1e3822
           have i₂ := b1e2118
           grind)
        | exact superpose b1e2118 b1e3822
        | exact resolve b1e3822 b1e2118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2118 b1e3822
      have b1e3832 : False := by grind
      exact b1e3832
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b2e30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b2e10 (σ x) (σ x) X0
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) X1) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b2e10 X1 (M.op X1 x) X3
           have i₂ := b2e10 X1 x X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 X1 (σ x)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b2e53 : x = (M.op y x) ∨ y = (M.op x x) := by
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
      have b2e56 : x = (M.op y x) := by
        first
        | (have r₁ := b2e53
           have r₂ := b2e17
           grind)
        | exact resolve b2e53 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53
      have b2e77 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = (M.op (σ y) (M.op X2 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e34 (M.op X2 X2) X0
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e34
        | exact resolve b2e34 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e79 : (M.op y x) = (M.op (σ y) y) := by
        first
        | (have i₁ := b2e34 y x
           have i₂ := b2e56
           grind)
        | exact superpose b2e56 b2e34
        | exact resolve b2e34 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e81 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (σ y) X0) := by
        intro X0 X2
        first
        | (have i₁ := b2e10 X0 x X2
           have i₂ := b2e34 X0 x
           grind)
        | exact superpose b2e34 b2e10
        | exact resolve b2e10 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e82 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X0 (M.op (σ y) X0)) := by
        intro X0 X2
        first
        | (have i₁ := b2e10 X0 (M.op X0 x) X2
           have i₂ := b2e34 X0 x
           grind)
        | exact superpose b2e34 b2e10
        | exact resolve b2e10 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e83 : x = (M.op (σ y) y) := by
        first
        | (have i₁ := b2e79
           have i₂ := b2e56
           grind)
        | exact superpose b2e56 b2e79
        | exact resolve b2e79 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e79
      have b2e84 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X2 X2)) = (M.op (σ y) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e77 X0 X1 X2
           have i₂ := b2e81 (M.op X0 (M.op X0 X1)) X2
           grind)
        | exact superpose b2e81 b2e77
        | exact resolve b2e77 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e77
      have b2e86 : ∀ X0 X2 : G, (M.op (σ y) (M.op X2 X2)) = (M.op (σ y) (M.op (σ y) X0)) := by
        intro X0 X2
        first
        | (have i₁ := b2e84 X0 x X2
           have i₂ := b2e34 X0 x
           grind)
        | exact superpose b2e34 b2e84
        | exact resolve b2e84 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e84
      have b2e87 : ∀ X2 : G, (M.op (σ y) (M.op X2 X2)) = (M.op (σ y) (σ y)) := by
        intro X2
        first
        | (have i₁ := b2e86 x X2
           have i₂ := b2e34 (σ y) x
           grind)
        | exact superpose b2e34 b2e86
        | exact resolve b2e86 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e86
      have b2e88 : (M.op (σ y) (σ y)) = (M.op (σ y) x) := by
        first
        | (have i₁ := b2e34 (σ y) y
           have i₂ := b2e83
           grind)
        | exact superpose b2e83 b2e34
        | exact resolve b2e34 b2e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e83
      have b2e538 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) = (M.op (M.op (M.op X0 X0) X2) (M.op (σ y) (M.op X0 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e31 X0 (M.op (M.op X0 X0) X2) X1
           have i₂ := b2e34 (M.op X0 X0) X2
           grind)
        | exact superpose b2e34 b2e31
        | exact resolve b2e31 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e588 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) = (M.op (M.op (M.op X0 X0) X2) (M.op (σ y) (σ y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e538 X0 X1 X2
           have i₂ := b2e87 X0
           grind)
        | exact superpose b2e87 b2e538
        | exact resolve b2e538 b2e87
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e87 b2e538
      have b2e620 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) = (M.op (M.op (M.op X0 X0) X2) (M.op (σ y) x)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e588 X0 X1 X2
           have i₂ := b2e88
           grind)
        | exact superpose b2e88 b2e588
        | exact resolve b2e588 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e588
      have b2e643 : ∀ X1 X2 : G, (M.op (M.op X1 X1) (M.op (σ y) X2)) = (M.op (M.op (σ y) X2) (M.op (σ y) x)) := by
        intro X1 X2
        first
        | (have i₁ := b2e620 X2 X1 x
           have i₂ := b2e81 x X2
           grind)
        | exact superpose b2e81 b2e620
        | exact resolve b2e620 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e620
      have b2e659 : ∀ X2 : G, (M.op (σ y) (M.op (σ y) X2)) = (M.op (M.op (σ y) X2) (M.op (σ y) x)) := by
        intro X2
        first
        | (have i₁ := b2e643 x X2
           have i₂ := b2e81 (M.op (σ y) X2) x
           grind)
        | exact superpose b2e81 b2e643
        | exact resolve b2e643 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e643
      have b2e673 : ∀ X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X2) (M.op (σ y) x)) := by
        intro X2
        first
        | (have i₁ := b2e659 X2
           have i₂ := b2e34 (σ y) X2
           grind)
        | exact superpose b2e34 b2e659
        | exact resolve b2e659 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e659
      have b2e678 : ∀ X2 : G, (M.op (σ y) x) = (M.op (M.op (σ y) X2) (M.op (σ y) x)) := by
        intro X2
        first
        | (have i₁ := b2e673 X2
           have i₂ := b2e88
           grind)
        | exact superpose b2e88 b2e673
        | exact resolve b2e673 b2e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e88 b2e673
      have b2e1711 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e51 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e51
        | exact resolve b2e51 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e2528 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e1711
           grind)
        | exact superpose b2e1711 b2e11
        | exact resolve b2e11 b2e1711
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1711
      have b2e2544 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e2528
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e2528
        | exact resolve b2e2528 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2528
      have b2e2551 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e48 x x
           have i₂ := b2e2544
           grind)
        | exact superpose b2e2544 b2e48
        | exact resolve b2e48 b2e2544
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48 b2e2544
      have b2e2554 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e2551
           have r₂ := b2e17
           grind)
        | exact resolve b2e2551 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2551
      have b2e2593 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e2554
           grind)
        | exact superpose b2e2554 b2e11
        | exact resolve b2e11 b2e2554
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2554
      have b2e2609 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e2593
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e2593
        | exact resolve b2e2593 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2593
      have b2e2610 : x = y := by grind
      clear b2e2609
      have b2e2632 : ∀ X0 : G, (M.op (σ y) x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ y) x)) := by
        intro X0
        first
        | (have i₁ := b2e678 (M.op (σ y) (σ y))
           have i₂ := b2e82 (σ y) X0
           grind)
        | exact superpose b2e82 b2e678
        | exact resolve b2e678 b2e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e82
      have b2e2671 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ y) X0) (M.op (σ y) x)) := by
        intro X0
        first
        | (have i₁ := b2e34 (M.op (σ y) X0) (M.op (σ y) x)
           have i₂ := b2e678 X0
           grind)
        | exact superpose b2e678 b2e34
        | exact resolve b2e34 b2e678
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2682 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ y) x) := by
        intro X0
        first
        | (have i₁ := b2e2671 X0
           have i₂ := b2e678 X0
           grind)
        | exact superpose b2e678 b2e2671
        | exact resolve b2e2671 b2e678
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e678 b2e2671
      have b2e2710 : ∀ X0 : G, (M.op (σ x) x) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) x)) := by
        intro X0
        first
        | (have i₁ := b2e2632 X0
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e2632
        | exact resolve b2e2632 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2632
      have b2e2719 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) x) := by
        intro X0
        first
        | (have i₁ := b2e2682 X0
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e2682
        | exact resolve b2e2682 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2682
      have b2e2731 : (M.op (σ x) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) x)) := by
        first
        | (have i₁ := b2e2710 x
           have i₂ := b2e30 x
           grind)
        | exact superpose b2e30 b2e2710
        | exact resolve b2e2710 b2e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30 b2e2710
      have b2e2739 : (M.op (σ y) (σ x)) = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e2719 x
           have i₂ := b2e34 (σ x) x
           grind)
        | exact superpose b2e34 b2e2719
        | exact resolve b2e2719 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2719
      have b2e2744 : (M.op (σ x) x) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) x)) := by
        first
        | (have i₁ := b2e2731
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e2731
        | exact resolve b2e2731 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2731
      have b2e2750 : (M.op (σ x) (σ x)) = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e2739
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e2739
        | exact resolve b2e2739 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2739
      have b2e2753 : (M.op (σ x) x) = (M.op (σ y) (M.op (σ x) x)) := by
        first
        | (have i₁ := b2e2744
           have i₂ := b2e81 (M.op (σ x) x) (σ x)
           grind)
        | exact superpose b2e81 b2e2744
        | exact resolve b2e2744 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e81 b2e2744
      have b2e2759 : (σ y) = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e2750
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e2750
        | exact resolve b2e2750 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2750
      have b2e2762 : (M.op (σ x) x) = (M.op (σ x) (M.op (σ x) x)) := by
        first
        | (have i₁ := b2e2753
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e2753
        | exact resolve b2e2753 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2753
      have b2e2768 : (σ x) = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e2759
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e2759
        | exact resolve b2e2759 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2759
      have b2e2771 : (M.op (σ y) (σ x)) = (M.op (σ x) x) := by
        first
        | (have i₁ := b2e2762
           have i₂ := b2e34 (σ x) x
           grind)
        | exact superpose b2e34 b2e2762
        | exact resolve b2e2762 b2e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34 b2e2762
      have b2e2779 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e2771
           have i₂ := b2e2768
           grind)
        | exact superpose b2e2768 b2e2771
        | exact resolve b2e2771 b2e2768
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2768 b2e2771
      have b2e2783 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e2779
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e2779
        | exact resolve b2e2779 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2779
      have b2e2787 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e16
        | exact resolve b2e16 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2792 : x = (M.op x x) := by
        first
        | (have i₁ := b2e56
           have i₂ := b2e2610
           grind)
        | exact superpose b2e2610 b2e56
        | exact resolve b2e56 b2e2610
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56 b2e2610
      have b2e2819 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e2787
           have i₂ := b2e2792
           grind)
        | exact superpose b2e2792 b2e2787
        | exact resolve b2e2787 b2e2792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2787 b2e2792
      have b2e2826 : False := by grind
      exact b2e2826
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
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
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
      have b3e22 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) X1) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e10 X1 (M.op X1 x) X3
           have i₂ := b3e10 X1 x X0
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e10 X1 x X3
           have i₂ := b3e10 X1 x X0
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e27 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
        intro X0
        grind
      have b3e31 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e27 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e27
        | exact resolve b3e27 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27
      have b3e35 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e37 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
      have b3e38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b3e41 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
      have b3e46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b3e120 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e31 X1
           have i₂ := b3e14 (τ X1) X0
           grind)
        | (have i₁ := b3e31 X0
           have i₂ := b3e14 X0 (M.op (τ X0) (τ X0))
           grind)
        | exact superpose b3e14 b3e31
        | (have j1 := b3e14 (τ X1) X0
           grind)
        | exact resolve b3e31 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e35 (σ X1) (σ X0)
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e35
        | exact resolve b3e35 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e140 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b3e35 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e148 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b3e46
      have b3e162 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e148 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e148
        | exact resolve b3e148 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e148
      have b3e208 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X2 X2) X1) ∨ (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e140 (M.op (M.op X2 X2) X1) X1
           have i₂ := b3e22 X2 X1 X0
           grind)
        | exact superpose b3e22 b3e140
        | (have j0 := b3e140 (M.op (M.op X2 X2) X1) X1
           grind)
        | (have r₁ := b3e140 (M.op (M.op x x) X1) X1
           have r₂ := b3e22 x X1 x
           grind)
        | exact resolve b3e140 b3e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e22 b3e140
      have b3e214 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
        intro X1 X2
        first
        | (have j0 := b3e208 x X1 X2
           grind)
        | (have r₁ := b3e208 x X1 x
           have r₂ := b3e24 x X1 x
           grind)
        | (have r₁ := b3e208 x X1 x
           have r₂ := b3e24 x X1 x
           grind)
        | exact resolve b3e208 b3e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e208
      have b3e215 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b3e37 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37
      have b3e216 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e215
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e215
        | exact resolve b3e215 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e215
      have b3e696 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e38 X1 X1
           have i₂ := b3e38 X0 X1
           grind)
        | exact superpose b3e38 b3e38
        | (have j0 := b3e38 X0 X1
           have j1 := b3e38 X0 X1
           grind)
        | exact resolve b3e38 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e697 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e38 X0 X0
           have i₂ := b3e14 (σ X0) X1
           grind)
        | (have i₁ := b3e38 X0 X1
           have i₂ := b3e14 X0 (M.op (σ X0) (σ X1))
           grind)
        | exact superpose b3e14 b3e38
        | (have j1 := b3e14 (σ X1) X0
           grind)
        | exact resolve b3e38 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e734 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 X1
           have i₂ := b3e38 X1 X0
           grind)
        | exact superpose b3e38 b3e11
        | (have j1 := b3e38 X1 X0
           grind)
        | exact resolve b3e11 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e747 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e162 X1
           have i₂ := b3e38 X0 X1
           grind)
        | exact superpose b3e38 b3e162
        | (have j1 := b3e38 X0 X1
           grind)
        | exact resolve b3e162 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e162
      have b3e767 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e38 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e771 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e747 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e747
        | (have j0 := b3e747 X0 X1
           grind)
        | exact resolve b3e747 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e747
      have b3e786 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X2) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e214 X1 X0
           have i₂ := b3e14 X0 X1
           grind)
        | (have i₁ := b3e214 X1 X2
           have i₂ := b3e14 X0 (M.op X2 X2)
           grind)
        | exact superpose b3e14 b3e214
        | (have j1 := b3e14 X1 X0
           grind)
        | exact resolve b3e214 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e214
      have b3e1903 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e41 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e41
        | exact resolve b3e41 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1940 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e12 X1
           have i₂ := b3e41 X1 X0
           grind)
        | exact superpose b3e41 b3e12
        | (have j1 := b3e41 X1 X0
           grind)
        | exact resolve b3e12 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e41
      have b3e2025 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e1903 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e1903
        | (have j0 := b3e1903 X0 X1
           grind)
        | exact resolve b3e1903 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1903
      have b3e2093 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e2146 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e31 X1
           have i₂ := b3e2025 X0 (τ X1)
           grind)
        | (have i₁ := b3e31 X0
           have i₂ := b3e2025 (M.op (τ X0) (τ X0)) X1
           grind)
        | exact superpose b3e2025 b3e31
        | (have j1 := b3e2025 X0 (τ X1)
           grind)
        | exact resolve b3e31 b3e2025
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31
      have b3e2151 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2146 X0 X1
           have i₂ := b3e20 X1 X0
           grind)
        | exact superpose b3e20 b3e2146
        | (have j0 := b3e2146 X0 X1
           grind)
        | exact resolve b3e2146 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20 b3e2146
      have b3e4052 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e14 (σ X0) X1
           have i₂ := b3e133 X0 X0
           grind)
        | exact superpose b3e133 b3e14
        | (have j0 := b3e14 (σ X0) X1
           have j1 := b3e133 X0 X0
           grind)
        | exact resolve b3e14 b3e133
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e4059 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (k X0 X0)) X2) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e24 X1 X2 (σ X0)
           have i₂ := b3e133 X0 X0
           grind)
        | exact superpose b3e133 b3e24
        | (have j1 := b3e133 X0 X0
           grind)
        | exact resolve b3e24 b3e133
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e4085 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 (σ X1) (σ X0) X2
           have i₂ := b3e133 X0 X1
           grind)
        | exact superpose b3e133 b3e10
        | (have j1 := b3e133 X0 X1
           grind)
        | exact resolve b3e10 b3e133
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e133
      have b3e4604 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e120 X0 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e120
        | (have j0 := b3e120 X1 (σ X0)
           grind)
        | exact resolve b3e120 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e120
      have b3e4667 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e4604 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e4604
        | (have j0 := b3e4604 X0 X1
           grind)
        | exact resolve b3e4604 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4604
      have b3e5333 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b3e767 X0
           have i₂ := b3e4667 X0 X0
           grind)
        | exact superpose b3e4667 b3e767
        | (have j0 := b3e767 X0
           have j1 := b3e4667 X0 X0
           grind)
        | (have r₁ := b3e767 x
           have r₂ := b3e4667 x x
           grind)
        | exact resolve b3e767 b3e4667
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e5363 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e5333 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e5333
      have b3e8853 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e734 X1 X1
           have i₂ := b3e38 X0 X1
           grind)
        | exact superpose b3e38 b3e734
        | (have j0 := b3e734 X1 X0
           have j1 := b3e38 X0 X1
           grind)
        | exact resolve b3e734 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38 b3e734
      have b3e8912 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e8853 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e8853
        | (have j0 := b3e8853 X0 X1
           grind)
        | exact resolve b3e8853 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e8853
      have b3e13926 : (σ y) ≠ (σ (k x x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e771 x x
           grind)
        | exact superpose b3e771 b3e18
        | (have j1 := b3e771 x x
           grind)
        | exact resolve b3e18 b3e771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e13927 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e771 x y
           grind)
        | exact superpose b3e771 b3e16
        | (have j1 := b3e771 x y
           grind)
        | exact resolve b3e16 b3e771
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e771
      have b3e14045 : y = (k y x) := by
        first
        | (have j1 := b3e2093 x y
           grind)
        | (have r₁ := b3e13927
           have r₂ := b3e2093 x y
           grind)
        | exact resolve b3e13927 b3e2093
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2093 b3e13927
      have b3e14695 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e2025 x y
           have i₂ := b3e14045
           grind)
        | exact superpose b3e14045 b3e2025
        | (have j0 := b3e2025 x y
           grind)
        | exact resolve b3e2025 b3e14045
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e16092 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e697 X0 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e697
        | (have j0 := b3e697 X1 (τ X0)
           grind)
        | exact resolve b3e697 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e16242 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e16092 X0 X1
           have i₂ := b3e21 X0 (τ X0)
           grind)
        | exact superpose b3e21 b3e16092
        | (have j0 := b3e16092 X0 X1
           grind)
        | exact resolve b3e16092 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21 b3e16092
      have b3e16253 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e16242 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e16242
        | (have j0 := b3e16242 X0 X1
           grind)
        | exact resolve b3e16242 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e16242
      have b3e31326 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (k x X0) = (M.op X0 x) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b3e13926
           have i₂ := b3e16253 x x
           grind)
        | (have i₁ := b3e13926
           have i₂ := b3e16253 X0 (k x x)
           grind)
        | exact superpose b3e16253 b3e13926
        | (have j1 := b3e16253 x X0
           grind)
        | (have r₁ := b3e13926
           have r₂ := b3e16253 (σ y) (σ (k x x))
           grind)
        | (have r₁ := b3e13926
           have r₂ := b3e16253 (σ (k x x)) (σ y)
           grind)
        | exact resolve b3e13926 b3e16253
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13926 b3e16253
      have b3e31331 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (k x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b3e31326 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31326
      have b3e51312 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X1 X1)
           have i₂ := b3e696 X0 X1
           grind)
        | (have i₁ := b3e11 X0
           have i₂ := b3e696 X0 X1
           grind)
        | exact superpose b3e696 b3e11
        | (have j1 := b3e696 X0 X1
           grind)
        | exact resolve b3e11 b3e696
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e696
      have b3e51380 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e51312 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e51312
        | (have j0 := b3e51312 X0 X1
           grind)
        | exact resolve b3e51312 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e51312
      have b3e51487 : (k x y) = (M.op y x) ∨ x = y := by
        first
        | (have j0 := b3e31331 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31331
      have b3e71588 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have j0 := b3e1940 (τ X0) X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1940
      have b3e71589 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e71588 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e71588
        | (have j0 := b3e71588 X0
           grind)
        | exact resolve b3e71588 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71588
      have b3e72384 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e71589 X0
           have i₂ := b3e35 X0 X0
           grind)
        | exact superpose b3e35 b3e71589
        | (have j0 := b3e71589 X0
           have j1 := b3e35 X0 X0
           grind)
        | (have r₁ := b3e71589 X0
           have r₂ := b3e35 X0 X0
           grind)
        | exact resolve b3e71589 b3e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e72426 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
        intro X0
        first
        | (have j0 := b3e72384 X0
           have j1 := b3e71589 X0
           grind)
        | (have r₁ := b3e72384 X0
           have r₂ := b3e71589 X0
           grind)
        | exact resolve b3e72384 b3e71589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71589 b3e72384
      have b3e73214 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b3e72426 (σ X0)
           have i₂ := b3e5363 X0
           grind)
        | exact superpose b3e5363 b3e72426
        | (have j0 := b3e72426 (σ X0)
           have j1 := b3e5363 X0
           grind)
        | (have r₁ := b3e72426 (σ X0)
           have r₂ := b3e5363 X0
           grind)
        | exact resolve b3e72426 b3e5363
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e5363 b3e72426
      have b3e73225 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e73214 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e73214
      have b3e73231 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have i₁ := b3e73225 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e73225
        | (have j0 := b3e73225 X0
           grind)
        | exact resolve b3e73225 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e73225
      have b3e76506 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e73231 X1
           have i₂ := b3e2025 X0 X1
           grind)
        | (have i₁ := b3e73231 X0
           have i₂ := b3e2025 (M.op X0 X0) X1
           grind)
        | exact superpose b3e2025 b3e73231
        | (have j1 := b3e2025 X0 X1
           grind)
        | exact resolve b3e73231 b3e2025
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e73231
      have b3e103067 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e2151 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e2151
        | (have j0 := b3e2151 X1 (σ X0)
           grind)
        | exact resolve b3e2151 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2151
      have b3e103112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e103067 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e103067
        | (have j0 := b3e103067 X0 X1
           grind)
        | exact resolve b3e103067 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e103067
      have b3e103118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e103112 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e103112
        | (have j0 := b3e103112 X0 X1
           grind)
        | exact resolve b3e103112 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e103112
      have b3e142365 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e767 X0
           have i₂ := b3e103118 X0 X0
           grind)
        | exact superpose b3e103118 b3e767
        | (have j0 := b3e767 X0
           have j1 := b3e103118 X0 X0
           grind)
        | (have r₁ := b3e767 x
           have r₂ := b3e103118 x x
           grind)
        | exact resolve b3e767 b3e103118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e103118
      have b3e142396 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e142365 X0
           have j1 := b3e767 X0
           grind)
        | (have r₁ := b3e142365 X0
           have r₂ := b3e767 X0
           grind)
        | exact resolve b3e142365 b3e767
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e767 b3e142365
      have b3e201678 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e8912 x y
           grind)
        | exact superpose b3e8912 b3e16
        | (have j1 := b3e8912 x y
           grind)
        | (have r₁ := b3e16
           have r₂ := b3e8912 (σ (M.op x y)) (M.op (σ x) (σ y))
           grind)
        | (have r₁ := b3e16
           have r₂ := b3e8912 (M.op (σ x) (σ y)) (σ (M.op x y))
           grind)
        | exact resolve b3e16 b3e8912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e8912
      have b3e201685 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b3e201678
           have i₂ := b3e14045
           grind)
        | exact superpose b3e14045 b3e201678
        | exact resolve b3e201678 b3e14045
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e201678
      have b3e201776 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e201685
           have i₂ := b3e14695
           grind)
        | exact superpose b3e14695 b3e201685
        | (have r₁ := b3e201685
           have r₂ := b3e14695
           grind)
        | exact resolve b3e201685 b3e14695
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e201685
      have b3e201777 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by grind
      clear b3e201776
      have b3e201794 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e11 (k y y)
           have i₂ := b3e201777
           grind)
        | exact superpose b3e201777 b3e11
        | exact resolve b3e11 b3e201777
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e201777
      have b3e201804 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e201794
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e201794
        | exact resolve b3e201794 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e201794
      have b3e201898 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e35 y y
           have i₂ := b3e201804
           grind)
        | exact superpose b3e201804 b3e35
        | exact resolve b3e35 b3e201804
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35 b3e201804
      have b3e201918 : x = (M.op y y) ∨ x = y := by grind
      clear b3e201898
      have b3e203085 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e51380 x y
           grind)
        | exact superpose b3e51380 b3e16
        | (have j1 := b3e51380 x y
           grind)
        | exact resolve b3e16 b3e51380
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e51380
      have b3e203086 : x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have j1 := b3e76506 x y
           grind)
        | (have r₁ := b3e203085
           have r₂ := b3e76506 (M.op x y) (k y x)
           grind)
        | (have r₁ := b3e203085
           have r₂ := b3e76506 (k y x) (M.op x y)
           grind)
        | (have r₁ := b3e203085
           have r₂ := b3e76506 x y
           grind)
        | exact resolve b3e203085 b3e76506
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e76506 b3e203085
      have b3e203121 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        intro X0 X1
        first
        | (have i₁ := b3e4059 y X1 x
           have i₂ := b3e203086
           grind)
        | exact superpose b3e203086 b3e4059
        | exact resolve b3e4059 b3e203086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4059
      have b3e203172 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e4667 y y
           have i₂ := b3e203086
           grind)
        | exact superpose b3e203086 b3e4667
        | exact resolve b3e4667 b3e203086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4667
      have b3e203192 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
      clear b3e203172
      have b3e203194 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ (σ x) = (σ y) := by
        intro X0 X1
        first
        | (have j0 := b3e203121 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e203121
      have b3e203242 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) ∨ (σ x) = (σ y) := by
        intro X0 X1
        first
        | (have i₁ := b3e24 X0 X1 y
           have i₂ := b3e203192
           grind)
        | exact superpose b3e203192 b3e24
        | exact resolve b3e24 b3e203192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e203192
      have b3e229888 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b3e203242 x X0
           have i₂ := b3e203194 x X0
           grind)
        | exact superpose b3e203194 b3e203242
        | exact resolve b3e203242 b3e203194
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e203194 b3e203242
      have b3e230032 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have j0 := b3e229888 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e229888
      have b3e230122 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e230032 (σ y)
           grind)
        | exact superpose b3e230032 b3e16
        | exact resolve b3e16 b3e230032
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e230032
      have b3e245725 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e4052 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4052
      have b3e245726 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e245725 X0 X1
           have j1 := b3e697 X1 X0
           grind)
        | (have r₁ := b3e245725 (k X1 X1) X0
           have r₂ := b3e697 X0 X1
           grind)
        | (have r₁ := b3e245725 X0 (σ (k X1 X1))
           have r₂ := b3e697 (σ X0) X1
           grind)
        | (have r₁ := b3e245725 X1 X0
           have r₂ := b3e697 X0 X1
           grind)
        | exact resolve b3e245725 b3e697
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e697 b3e245725
      have b3e245748 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X1 X1)
           have i₂ := b3e245726 X1 X0
           grind)
        | (have i₁ := b3e11 X0
           have i₂ := b3e245726 X0 (σ X0)
           grind)
        | exact superpose b3e245726 b3e11
        | (have j1 := b3e245726 X1 X0
           grind)
        | exact resolve b3e11 b3e245726
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e245726
      have b3e246208 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e245748 (σ X0) X1
           grind)
        | exact superpose b3e245748 b3e15
        | (have j1 := b3e245748 (σ X0) X1
           grind)
        | exact resolve b3e15 b3e245748
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e245748
      have b3e246214 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e246208 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e246208
        | (have j0 := b3e246208 X0 X1
           grind)
        | exact resolve b3e246208 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e246208
      have b3e246822 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e246214 x y
           grind)
        | exact superpose b3e246214 b3e16
        | (have j1 := b3e246214 x y
           grind)
        | exact resolve b3e16 b3e246214
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e246214
      have b3e246907 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e246822
           have i₂ := b3e14045
           grind)
        | exact superpose b3e14045 b3e246822
        | exact resolve b3e246822 b3e14045
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14045 b3e246822
      have b3e247028 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e246907
           have i₂ := b3e14695
           grind)
        | exact superpose b3e14695 b3e246907
        | (have r₁ := b3e246907
           have r₂ := b3e14695
           grind)
        | exact resolve b3e246907 b3e14695
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14695
      have b3e247029 : x = (k y y) ∨ x = (M.op y y) := by grind
      clear b3e247028
      have b3e247202 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e14 y y
           have i₂ := b3e247029
           grind)
        | exact superpose b3e247029 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e247029
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e247029
      have b3e247239 : y = (M.op y y) ∨ x = (M.op y y) := by grind
      clear b3e247202
      have b3e247861 : x ≠ y ∨ x = (M.op y y) := by grind
      clear b3e247239
      have b3e247880 : x = (M.op y y) := by
        first
        | (have r₁ := b3e247861
           have r₂ := b3e201918
           grind)
        | exact resolve b3e247861 b3e201918
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e201918 b3e247861
      have b3e247941 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X0 X1 y
           have i₂ := b3e247880
           grind)
        | exact superpose b3e247880 b3e10
        | exact resolve b3e10 b3e247880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e247946 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e24 X0 X1 y
           have i₂ := b3e247880
           grind)
        | exact superpose b3e247880 b3e24
        | exact resolve b3e24 b3e247880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24
      have b3e248478 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b3e142396 y
           have i₂ := b3e247880
           grind)
        | exact superpose b3e247880 b3e142396
        | (have j0 := b3e142396 y
           grind)
        | exact resolve b3e142396 b3e247880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e142396
      have b3e248569 : ∀ X0 : G, x = (k x y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e786 y x y
           have i₂ := b3e247880
           grind)
        | exact superpose b3e247880 b3e786
        | (have j0 := b3e786 y X0 x
           grind)
        | exact resolve b3e786 b3e247880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e786
      have b3e249259 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b3e247941 y y
           have i₂ := b3e247880
           grind)
        | exact superpose b3e247880 b3e247941
        | exact resolve b3e247941 b3e247880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e247941
      have b3e266069 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e2025 y x
           have i₂ := b3e248569 X0
           grind)
        | exact superpose b3e248569 b3e2025
        | (have j0 := b3e2025 y x
           have j1 := b3e248569 X0
           grind)
        | exact resolve b3e2025 b3e248569
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2025 b3e248569
      have b3e266160 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b3e266069 X0
           grind)
        | (have r₁ := b3e266069 X0
           have r₂ := b3e17
           grind)
        | exact resolve b3e266069 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e266069
      have b3e266166 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e266160 X0
           have i₂ := b3e249259
           grind)
        | exact superpose b3e249259 b3e266160
        | (have j0 := b3e266160 X0
           grind)
        | exact resolve b3e266160 b3e249259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e266160
      have b3e320671 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ x = (k y y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b3e246907
           have i₂ := b3e266166 X0
           grind)
        | exact superpose b3e266166 b3e246907
        | (have j1 := b3e266166 X0
           grind)
        | exact resolve b3e246907 b3e266166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e246907 b3e266166
      have b3e320691 : ∀ X0 : G, x = (k y y) ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b3e320671 X0
           grind)
        | (have r₁ := b3e320671 X0
           have r₂ := b3e203086
           grind)
        | exact resolve b3e320671 b3e203086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e203086 b3e320671
      have b3e321296 : x ≠ (M.op y y) ∨ x = (k y y) := by grind
      clear b3e320691
      have b3e321299 : x = (k y y) := by
        first
        | (have r₁ := b3e321296
           have r₂ := b3e247880
           grind)
        | exact resolve b3e321296 b3e247880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e321296
      have b3e321849 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 X0) (σ y)) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b3e4085 y y x
           have i₂ := b3e321299
           grind)
        | exact superpose b3e321299 b3e4085
        | exact resolve b3e4085 b3e321299
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e4085 b3e321299
      have b3e321878 : (M.op (σ y) (σ x)) = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e321849 x
           have i₂ := b3e247946 x (σ y)
           grind)
        | exact superpose b3e247946 b3e321849
        | exact resolve b3e321849 b3e247946
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e247946 b3e321849
      have b3e321889 : (σ (k x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b3e321878
           have i₂ := b3e216
           grind)
        | exact superpose b3e216 b3e321878
        | exact resolve b3e321878 b3e216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e216 b3e321878
      have b3e329652 : (σ (M.op y x)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b3e321889
           have i₂ := b3e51487
           grind)
        | exact superpose b3e51487 b3e321889
        | exact resolve b3e321889 b3e51487
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e51487 b3e321889
      have b3e329655 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b3e329652
           have i₂ := b3e249259
           grind)
        | exact superpose b3e249259 b3e329652
        | exact resolve b3e329652 b3e249259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e249259 b3e329652
      have b3e329656 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b3e329655
           have r₂ := b3e230122
           grind)
        | exact resolve b3e329655 b3e230122
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e230122 b3e329655
      have b3e329680 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b3e11 y
           have i₂ := b3e329656
           grind)
        | exact superpose b3e329656 b3e11
        | exact resolve b3e11 b3e329656
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e329656
      have b3e329750 : x = y ∨ x = y := by
        first
        | (have i₁ := b3e329680
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e329680
        | exact resolve b3e329680 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e329680
      have b3e329751 : x = y := by grind
      clear b3e329750
      have b3e329763 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e329751
           grind)
        | exact superpose b3e329751 b3e16
        | exact resolve b3e16 b3e329751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e329840 : x = (M.op x x) := by
        first
        | (have i₁ := b3e247880
           have i₂ := b3e329751
           grind)
        | exact superpose b3e329751 b3e247880
        | exact resolve b3e247880 b3e329751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e247880
      have b3e329848 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e248478
           have i₂ := b3e329751
           grind)
        | exact superpose b3e329751 b3e248478
        | exact resolve b3e248478 b3e329751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e248478 b3e329751
      have b3e329897 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e329848
      have b3e329932 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e329763
           have i₂ := b3e329840
           grind)
        | exact superpose b3e329840 b3e329763
        | exact resolve b3e329763 b3e329840
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e329763 b3e329840
      have b3e329945 : False := by grind
      exact b3e329945

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4423 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4423 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : x = (M.op y y) := by grind
      have b0e18 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e33 X0 x
           have i₂ := b0e34 X0 x
           grind)
        | exact superpose b0e34 b0e33
        | exact resolve b0e33 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e39 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e36 (σ y)
           grind)
        | exact superpose b0e36 b0e16
        | exact resolve b0e16 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (M.op X0 X3) = (k X0 X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X3
           have i₂ := b0e14 X0 X3
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 (M.op X2 X2) X1
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X0 X3
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e58 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X0 X1
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 (M.op X0 X1) X1
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X0 X1
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b0e64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op x X1) ∨ (M.op X0 X3) = (k X0 X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e56 X0 X1 x X3
           have i₂ := b0e34 X1 x
           grind)
        | exact superpose b0e34 b0e56
        | (have j0 := b0e56 X0 X1 x X3
           grind)
        | exact resolve b0e56 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e65 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e34 X0 (M.op X0 x)
           have i₂ := b0e34 X0 x
           grind)
        | exact superpose b0e34 b0e34
        | exact resolve b0e34 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : (M.op (σ y) (σ x)) = (M.op x (σ y)) := by
        first
        | (have i₁ := b0e34 (σ y) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e34
        | exact resolve b0e34 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e34 y y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e34
        | exact resolve b0e34 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X0 (M.op x X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 X0 (M.op X0 x) X2
           have i₂ := b0e34 X0 x
           grind)
        | exact superpose b0e34 b0e10
        | exact resolve b0e10 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 : G, (M.op x (σ x)) = (M.op x (M.op (σ x) X0)) := by
        intro X0
        first
        | (have i₁ := b0e36 (M.op (σ x) X0)
           have i₂ := b0e34 (σ x) X0
           grind)
        | exact superpose b0e34 b0e36
        | exact resolve b0e36 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 : G, (M.op x (σ x)) = (M.op x (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e76 X0
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e76
        | exact resolve b0e76 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e82 : (M.op x (σ x)) = (M.op x x) := by
        first
        | (have i₁ := b0e77 x
           have i₂ := b0e34 x x
           grind)
        | exact superpose b0e34 b0e77
        | exact resolve b0e77 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e361 : (M.op x (σ y)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e71
           grind)
        | exact superpose b0e71 b0e39
        | exact resolve b0e39 b0e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e71
      have b0e406 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b0e65 (M.op x x)
           have i₂ := b0e34 x x
           grind)
        | exact superpose b0e34 b0e65
        | exact resolve b0e65 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e448 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e57 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e1295 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) x) ∨ (M.op X1 X3) = (k X1 X3) ∨ (M.op X2 x) = (k X2 x) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e64 X1 X2 X3
           have i₂ := b0e58 X2 x X0
           grind)
        | exact superpose b0e58 b0e64
        | (have j0 := b0e64 X1 X1 X3
           have j1 := b0e58 X1 X3 X2
           grind)
        | exact resolve b0e64 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58 b0e64
      have b0e1309 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op x (M.op x x)) ∨ (M.op X1 X3) = (k X1 X3) ∨ (M.op X2 x) = (k X2 x) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e1295 x X1 X2 X3
           have i₂ := b0e75 x x
           grind)
        | exact superpose b0e75 b0e1295
        | (have j0 := b0e1295 x X1 X2 X3
           grind)
        | exact resolve b0e1295 b0e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75 b0e1295
      have b0e1397 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op x x) ∨ (M.op X1 X3) = (k X1 X3) ∨ (M.op X2 x) = (k X2 x) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e1309 X1 X2 X3
           have i₂ := b0e34 x x
           grind)
        | exact superpose b0e34 b0e1309
        | (have j0 := b0e1309 X1 X2 X3
           grind)
        | exact resolve b0e1309 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e1309
      have b0e1618 : ∀ X0 : G, (σ X0) = (M.op x (σ x)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x)
           have i₂ := b0e61 X0 x
           grind)
        | exact superpose b0e61 b0e36
        | (have j1 := b0e61 X0 x
           grind)
        | exact resolve b0e36 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e61
      have b0e1652 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e1618 X0
           have i₂ := b0e82
           grind)
        | exact superpose b0e82 b0e1618
        | (have j0 := b0e1618 X0
           grind)
        | exact resolve b0e1618 b0e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82 b0e1618
      have b0e4766 : (M.op x (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op x x) := by
        first
        | (have i₁ := b0e69
           have i₂ := b0e1652 y
           grind)
        | exact superpose b0e1652 b0e69
        | (have j1 := b0e1652 y
           grind)
        | exact resolve b0e69 b0e1652
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69 b0e1652
      have b0e15446 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op x x) ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e1397 X0 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1397
      have b0e15447 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e15446 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15446
      have b0e22675 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e448 X0 X0
           have i₂ := b0e15447 X0
           grind)
        | (have i₁ := b0e448 x x
           have i₂ := b0e15447 X0
           grind)
        | exact superpose b0e15447 b0e448
        | (have j0 := b0e448 X0 X0
           have j1 := b0e15447 X0
           grind)
        | (have r₁ := b0e448 (M.op x x) (M.op x x)
           have r₂ := b0e15447 (M.op x x)
           grind)
        | exact resolve b0e448 b0e15447
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e448 b0e15447
      have b0e22841 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e22675 X0
           have j1 := b0e14 X0 x
           grind)
        | (have r₁ := b0e22675 X0
           have r₂ := b0e14 X0 x
           grind)
        | (have r₁ := b0e22675 (M.op x x)
           have r₂ := b0e14 (M.op x x) x
           grind)
        | (have r₁ := b0e22675 (k x x)
           have r₂ := b0e14 x x
           grind)
        | exact resolve b0e22675 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22675
      have b0e23707 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e22841 X0
           grind)
        | exact superpose b0e22841 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e22841 X0
           grind)
        | exact resolve b0e14 b0e22841
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22841
      have b0e23784 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 x) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e23707 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23707
      have b0e43488 : (M.op x (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op x x) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e4766
           have i₂ := b0e23784 y
           grind)
        | exact superpose b0e23784 b0e4766
        | (have j1 := b0e23784 y
           grind)
        | exact resolve b0e4766 b0e23784
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4766 b0e23784
      have b0e43656 : (σ y) = (M.op x x) ∨ y = (M.op y y) := by
        first
        | (have r₁ := b0e43488
           have r₂ := b0e361
           grind)
        | exact resolve b0e43488 b0e361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e361 b0e43488
      have b0e43667 : (σ y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e43656
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e43656
        | exact resolve b0e43656 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43656
      have b0e43691 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e406 x
           have i₂ := b0e43667
           grind)
        | exact superpose b0e43667 b0e406
        | exact resolve b0e406 b0e43667
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e406 b0e43667
      have b0e43757 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e43691
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e43691
        | exact resolve b0e43691 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43691
      have b0e44095 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e11 x
           have i₂ := b0e43757
           grind)
        | exact superpose b0e43757 b0e11
        | exact resolve b0e11 b0e43757
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43757
      have b0e44224 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e44095
           have i₂ := b0e11 y
           grind)
        | exact superpose b0e11 b0e44095
        | exact resolve b0e44095 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44095
      have b0e44225 : x = y := by grind
      clear b0e44224
      have b0e44721 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e44225
           grind)
        | exact superpose b0e44225 b0e16
        | exact resolve b0e16 b0e44225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44225
      have b0e44868 : (σ x) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e44721
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e44721
        | exact resolve b0e44721 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44721
      have b0e44916 : False := by grind
      exact b0e44916
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : x = (M.op y y) := by grind
      have b1e18 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e20 : y = (k x y) := by grind
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b1e26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11 (k (τ X0) X1)
           have i₂ := b1e21 X0 X1
           grind)
        | exact superpose b1e21 b1e11
        | exact resolve b1e11 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21
      have b1e30 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 X1 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e33 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b1e30 y y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e30
        | exact resolve b1e30 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30
      have b1e48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b1e51 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (σ y)
           grind)
        | (have i₁ := b1e18
           have i₂ := b1e14 (M.op (σ y) (σ y)) x
           grind)
        | exact superpose b1e14 b1e18
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e14 (σ x) (σ y)
           grind)
        | exact resolve b1e18 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b1e414 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e48 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48
      have b1e580 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
        intro X0
        grind
      clear b1e26
      have b1e586 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e580 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e580
        | exact resolve b1e580 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e580
      have b1e587 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e51 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e588 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e587
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e587
        | exact resolve b1e587 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e587
      have b1e589 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e588
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e588
        | exact resolve b1e588 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e588
      have b1e590 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e589
           grind)
        | exact superpose b1e589 b1e16
        | exact resolve b1e16 b1e589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e589
      have b1e599 : (σ y) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b1e590
           have i₂ := b1e33
           grind)
        | exact superpose b1e33 b1e590
        | exact resolve b1e590 b1e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e33 b1e590
      have b1e1081 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e52 y y
           grind)
        | exact superpose b1e52 b1e18
        | (have j1 := b1e52 y y
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e52 x y
           grind)
        | exact resolve b1e18 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52
      have b1e1243 : x ≠ y ∨ y = (k y y) := by
        first
        | (have i₁ := b1e414 y y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e414
        | (have j0 := b1e414 y y
           grind)
        | exact resolve b1e414 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e414
      have b1e1957 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e1081
           have i₂ := b1e14 y y
           grind)
        | exact superpose b1e14 b1e1081
        | (have j1 := b1e14 (σ y) (σ y)
           grind)
        | exact resolve b1e1081 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1081
      have b1e1973 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e1957
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1957
        | exact resolve b1e1957 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1957
      have b1e1974 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
      clear b1e1973
      have b1e1977 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b1e1974
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1974
        | exact resolve b1e1974 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1974
      have b1e1983 : y = (k (τ (σ y)) y) ∨ x = y := by
        first
        | (have i₁ := b1e586 y
           have i₂ := b1e1977
           grind)
        | exact superpose b1e1977 b1e586
        | exact resolve b1e586 b1e1977
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e586 b1e1977
      have b1e2020 : y = (k y y) ∨ x = y := by
        first
        | (have i₁ := b1e1983
           have i₂ := b1e11 y
           grind)
        | exact superpose b1e11 b1e1983
        | exact resolve b1e1983 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1983
      have b1e2025 : y = (k y y) := by
        first
        | (have r₁ := b1e2020
           have r₂ := b1e1243
           grind)
        | exact resolve b1e2020 b1e1243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1243 b1e2020
      have b1e2045 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e14 y y
           have i₂ := b1e2025
           grind)
        | exact superpose b1e2025 b1e14
        | (have j0 := b1e14 y y
           grind)
        | exact resolve b1e14 b1e2025
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2025
      have b1e2050 : y = (M.op y y) := by grind
      clear b1e2045
      have b1e2080 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e2050
           grind)
        | exact superpose b1e2050 b1e17
        | exact resolve b1e17 b1e2050
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2050
      have b1e2325 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e599
           have i₂ := b1e2080
           grind)
        | exact superpose b1e2080 b1e599
        | exact resolve b1e599 b1e2080
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e599
      have b1e2339 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e2325
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e2325
        | exact resolve b1e2325 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2325
      have b1e2351 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e2339
           have i₂ := b1e2080
           grind)
        | exact superpose b1e2080 b1e2339
        | exact resolve b1e2339 b1e2080
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2080 b1e2339
      have b1e2352 : False := by grind
      exact b1e2352
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b2e17 : x ≠ (M.op y y) := by grind
      have b2e18 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e20 : (σ y) = (k (σ x) (σ y)) := by grind
      have b2e21 : (σ y) = (σ (k x y)) := by
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
      have b2e34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 X1 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b2e52 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b2e21
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e21
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e21 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e21
      have b2e53 : (σ (M.op x y)) = (σ y) := by
        first
        | (have r₁ := b2e52
           have r₂ := b2e17
           grind)
        | exact resolve b2e52 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e78 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e34 (σ y) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e34
        | exact resolve b2e34 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e1706 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e49 y y
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e49
        | exact resolve b2e49 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e1963 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e78
           grind)
        | exact superpose b2e78 b2e16
        | exact resolve b2e16 b2e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e78
      have b2e1980 : (σ y) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e1963
           have i₂ := b2e53
           grind)
        | exact superpose b2e53 b2e1963
        | exact resolve b2e1963 b2e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53 b2e1963
      have b2e2526 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k y y)
           have i₂ := b2e1706
           grind)
        | exact superpose b2e1706 b2e11
        | exact resolve b2e11 b2e1706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1706
      have b2e2542 : x = (k y y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e2526
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e2526
        | exact resolve b2e2526 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2526
      have b2e2566 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e46 y y
           have i₂ := b2e2542
           grind)
        | exact superpose b2e2542 b2e46
        | exact resolve b2e46 b2e2542
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46 b2e2542
      have b2e2569 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e2566
           have r₂ := b2e17
           grind)
        | exact resolve b2e2566 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2566
      have b2e2705 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b2e11 x
           have i₂ := b2e2569
           grind)
        | exact superpose b2e2569 b2e11
        | exact resolve b2e11 b2e2569
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2569
      have b2e2721 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e2705
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e2705
        | exact resolve b2e2705 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2705
      have b2e2722 : x = y := by grind
      clear b2e2721
      have b2e2786 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e1980
           have i₂ := b2e2722
           grind)
        | exact superpose b2e2722 b2e1980
        | exact resolve b2e1980 b2e2722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1980
      have b2e2788 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e2786
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e2786
        | exact resolve b2e2786 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2786
      have b2e2796 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b2e2788
           have i₂ := b2e2722
           grind)
        | exact superpose b2e2722 b2e2788
        | exact resolve b2e2788 b2e2722
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2722 b2e2788
      have b2e2797 : False := by grind
      exact b2e2797
    · have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : x ≠ (M.op y y) := by grind
      have b3e18 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e35 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | (have i₁ := b3e18
           have i₂ := b3e14 (M.op (σ y) (σ y)) x
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 (σ x) (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e214 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e35 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35
      have b3e215 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e214
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e214
        | exact resolve b3e214 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e214
      have b3e216 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e215
           grind)
        | exact superpose b3e215 b3e16
        | exact resolve b3e16 b3e215
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e215
      have b3e277 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e216
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e216
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e216 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e216
      have b3e278 : x = (M.op y y) := by grind
      clear b3e277
      have b3e280 : False := by grind
      exact b3e280

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4423 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4423 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : x = (M.op y y) := by grind
        have b0e19 : (σ x) = (M.op (σ y) (σ y)) := by grind
        have b0e20 : y = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e37 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 X0 X1 x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 X0 X1 y
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e132 : y = (M.op x y) := by
          first
          | (have i₁ := b0e38 x x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e38
          | exact resolve b0e38 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e138 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e37 X0 x
             have i₂ := b0e38 X0 x
             grind)
          | exact superpose b0e38 b0e37
          | exact resolve b0e37 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37 b0e38
        have b0e150 : y = (M.op y y) := by
          first
          | (have i₁ := b0e132
             have i₂ := b0e138 y
             grind)
          | exact superpose b0e138 b0e132
          | exact resolve b0e132 b0e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e132 b0e138
        have b0e195 : x = y := by
          first
          | (have i₁ := b0e18
             have i₂ := b0e150
             grind)
          | exact superpose b0e150 b0e18
          | exact resolve b0e18 b0e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e150
        have b0e408 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e195
             grind)
          | exact superpose b0e195 b0e17
          | exact resolve b0e17 b0e195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e195
        have b0e417 : (σ x) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e408
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e408
          | exact resolve b0e408 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e408
        have b0e418 : False := by grind
        exact b0e418
      · have b1e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : x = (M.op y y) := by grind
        have b1e19 : (σ x) = (M.op (σ y) (σ y)) := by grind
        have b1e20 : y ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b1e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e30 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e11 X1 x X3
             have i₂ := b1e11 X1 x X0
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 X1 (σ y)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 X1 y
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e31 X0 x
             have i₂ := b1e32 X0 x
             grind)
          | exact superpose b1e32 b1e31
          | exact resolve b1e31 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e37 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e34 (σ y)
             grind)
          | exact superpose b1e34 b1e17
          | exact resolve b1e17 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (σ x) = (k (M.op x (σ x)) (σ x)) := by grind
        have b1e54 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (k X0 X3) = (M.op X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X1 X2 X3
             have i₂ := b1e15 X0 X3
             grind)
          | (have i₁ := b1e11 X0 X1 X2
             have i₂ := b1e15 (M.op X2 X2) X1
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 X0 X3
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X1 X1 X2
             have i₂ := b1e15 X0 X1
             grind)
          | (have i₁ := b1e11 X0 X1 X2
             have i₂ := b1e15 (M.op X0 X1) X1
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 X0 X1
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X1 X0
             have i₂ := b1e15 (σ X1) (σ X0)
             grind)
          | exact superpose b1e15 b1e16
          | (have j1 := b1e15 (σ X1) (σ X0)
             grind)
          | exact resolve b1e16 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op x X1) ∨ (k X0 X3) = (M.op X3 X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e54 X0 X1 x X3
             have i₂ := b1e32 X1 x
             grind)
          | exact superpose b1e32 b1e54
          | (have j0 := b1e54 X0 X1 x X3
             grind)
          | exact resolve b1e54 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e67 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = (M.op x (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e32 (M.op X2 X2) X0
             have i₂ := b1e11 X0 X1 X2
             grind)
          | exact superpose b1e11 b1e32
          | exact resolve b1e32 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e70 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e32 y y
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e32
          | exact resolve b1e32 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op x X0) := by
          intro X0 X2
          first
          | (have i₁ := b1e11 X0 x X2
             have i₂ := b1e32 X0 x
             grind)
          | exact superpose b1e32 b1e11
          | exact resolve b1e11 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op X0 (M.op x X0)) := by
          intro X0 X2
          first
          | (have i₁ := b1e11 X0 (M.op X0 x) X2
             have i₂ := b1e32 X0 x
             grind)
          | exact superpose b1e32 b1e11
          | exact resolve b1e11 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : ∀ X0 : G, (M.op x (σ x)) = (M.op x (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e34 (M.op (σ x) X0)
             have i₂ := b1e32 (σ x) X0
             grind)
          | exact superpose b1e32 b1e34
          | exact resolve b1e34 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : ∀ X0 : G, (M.op x (σ x)) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e75 X0
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e75
          | exact resolve b1e75 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e79 : ∀ X0 X1 X2 : G, (M.op x (M.op X2 X2)) = (M.op x (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e67 X0 X1 X2
             have i₂ := b1e73 (M.op X0 (M.op X0 X1)) X2
             grind)
          | exact superpose b1e73 b1e67
          | exact resolve b1e67 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e81 : (M.op x x) = (M.op x (σ x)) := by
          first
          | (have i₁ := b1e76 x
             have i₂ := b1e32 x x
             grind)
          | exact superpose b1e32 b1e76
          | exact resolve b1e76 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e84 : ∀ X0 X2 : G, (M.op x (M.op x X0)) = (M.op x (M.op X2 X2)) := by
          intro X0 X2
          first
          | (have i₁ := b1e79 X0 x X2
             have i₂ := b1e32 X0 x
             grind)
          | exact superpose b1e32 b1e79
          | exact resolve b1e79 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e85 : ∀ X2 : G, (M.op x x) = (M.op x (M.op X2 X2)) := by
          intro X2
          first
          | (have i₁ := b1e84 x X2
             have i₂ := b1e32 x x
             grind)
          | exact superpose b1e32 b1e84
          | exact resolve b1e84 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e87 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e25 X1 X0
             have i₂ := b1e15 (τ X1) X0
             grind)
          | exact superpose b1e15 b1e25
          | (have j1 := b1e15 (τ X1) X0
             grind)
          | exact resolve b1e25 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e140 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1)) := by
          intro X0 X1
          grind
        clear b1e30
        have b1e149 : ∀ X1 : G, (M.op X1 X1) = (k (M.op x (M.op X1 X1)) (M.op X1 X1)) := by
          intro X1
          first
          | (have i₁ := b1e140 x X1
             have i₂ := b1e73 (M.op X1 X1) x
             grind)
          | exact superpose b1e73 b1e140
          | exact resolve b1e140 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e140
        have b1e179 : ∀ X1 : G, (M.op X1 X1) = (k (M.op x x) (M.op X1 X1)) := by
          intro X1
          first
          | (have i₁ := b1e149 X1
             have i₂ := b1e85 X1
             grind)
          | exact superpose b1e85 b1e149
          | exact resolve b1e149 b1e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85 b1e149
        have b1e221 : (M.op x (σ y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e37
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e37
          | exact resolve b1e37 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e537 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e859 : (σ x) = (k (M.op x x) (σ x)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e81
             grind)
          | exact superpose b1e81 b1e39
          | exact resolve b1e39 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e1284 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X0 X0) x) ∨ (k X1 X3) = (M.op X3 X1) ∨ (M.op x X2) = (k X2 x) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e62 X1 X2 X3
             have i₂ := b1e56 X2 x X0
             grind)
          | exact superpose b1e56 b1e62
          | (have j0 := b1e62 X1 X1 X3
             have j1 := b1e56 X1 X3 X2
             grind)
          | exact resolve b1e62 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e1323 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (M.op X2 X2) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X1 X0
             have i₂ := b1e56 (σ X1) (σ X0) X2
             grind)
          | exact superpose b1e56 b1e16
          | (have j1 := b1e56 (σ X1) (σ X0) X2
             grind)
          | exact resolve b1e16 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e1326 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op x (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e1323 X0 X1 x
             have i₂ := b1e73 (σ X0) x
             grind)
          | exact superpose b1e73 b1e1323
          | (have j0 := b1e1323 X0 X1 x
             grind)
          | exact resolve b1e1323 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73 b1e1323
        have b1e1357 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (M.op x (M.op x x)) ∨ (k X1 X3) = (M.op X3 X1) ∨ (M.op x X2) = (k X2 x) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e1284 x X1 X2 X3
             have i₂ := b1e74 x x
             grind)
          | exact superpose b1e74 b1e1284
          | (have j0 := b1e1284 x X1 X2 X3
             grind)
          | exact resolve b1e1284 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74 b1e1284
        have b1e1443 : ∀ X1 X2 X3 : G, (M.op x x) = (M.op X1 X2) ∨ (k X1 X3) = (M.op X3 X1) ∨ (M.op x X2) = (k X2 x) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e1357 X1 X2 X3
             have i₂ := b1e32 x x
             grind)
          | exact superpose b1e32 b1e1357
          | (have j0 := b1e1357 X1 X2 X3
             grind)
          | exact resolve b1e1357 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e1357
        have b1e1806 : ∀ X0 : G, (σ X0) = (M.op x (σ x)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e34 (σ x)
             have i₂ := b1e59 x X0
             grind)
          | exact superpose b1e59 b1e34
          | (have j1 := b1e59 x X0
             grind)
          | exact resolve b1e34 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e1841 : ∀ X0 : G, (σ X0) = (M.op x x) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e1806 X0
             have i₂ := b1e81
             grind)
          | exact superpose b1e81 b1e1806
          | (have j0 := b1e1806 X0
             grind)
          | exact resolve b1e1806 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81 b1e1806
        have b1e1871 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b1e1841 X0
             have i₂ := b1e34 (σ X0)
             grind)
          | exact superpose b1e34 b1e1841
          | (have j0 := b1e1841 X0
             grind)
          | exact resolve b1e1841 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1841
        have b1e2027 : ∀ X0 : G, (σ x) ≠ (M.op x X0) ∨ (σ x) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e537 X0 (σ x)
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e537
          | (have j0 := b1e537 X0 (σ x)
             grind)
          | exact resolve b1e537 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e3402 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e87 X0 (σ X0)
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e87
          | exact resolve b1e87 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e3505 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e3402 X0 X1
             have i₂ := b1e16 X0 X1
             grind)
          | exact superpose b1e16 b1e3402
          | (have j0 := b1e3402 X0 X1
             grind)
          | exact resolve b1e3402 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3402
        have b1e9486 : (σ x) = (σ (k y y)) ∨ (σ x) = (M.op x (σ y)) := by
          first
          | (have i₁ := b1e1326 y y
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e1326
          | exact resolve b1e1326 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1326
        have b1e15764 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ (M.op x x) = (M.op X0 X0) ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e1443 X0 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1443
        have b1e15765 : ∀ X0 : G, (M.op x x) = (M.op X0 X0) ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e15764 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15764
        have b1e15903 : (k y y) = (τ (σ x)) ∨ (σ x) = (M.op x (σ y)) := by
          first
          | (have i₁ := b1e12 (k y y)
             have i₂ := b1e9486
             grind)
          | exact superpose b1e9486 b1e12
          | exact resolve b1e12 b1e9486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9486
        have b1e15971 : (σ x) = (M.op x (σ y)) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e15903
             have i₂ := b1e12 x
             grind)
          | exact superpose b1e12 b1e15903
          | exact resolve b1e15903 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15903
        have b1e16551 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e2027 (σ y)
             have i₂ := b1e15971
             grind)
          | exact superpose b1e15971 b1e2027
          | (have j0 := b1e2027 (σ y)
             grind)
          | (have r₁ := b1e2027 (σ y)
             have r₂ := b1e15971
             grind)
          | exact resolve b1e2027 b1e15971
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2027
        have b1e16568 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y y) := by grind
        clear b1e16551
        have b1e16574 : (σ x) = (σ (k y x)) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e16568
             have i₂ := b1e16 y x
             grind)
          | exact superpose b1e16 b1e16568
          | exact resolve b1e16568 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16568
        have b1e16935 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e3505 y x
             have i₂ := b1e16574
             grind)
          | exact superpose b1e16574 b1e3505
          | (have j0 := b1e3505 y x
             grind)
          | exact resolve b1e3505 b1e16574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3505 b1e16574
        have b1e17005 : (σ (M.op x y)) = (σ x) ∨ x = (k y y) := by
          first
          | (have r₁ := b1e16935
             have r₂ := b1e20
             grind)
          | exact resolve b1e16935 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16935
        have b1e17035 : (σ x) = (σ (M.op y x)) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e17005
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e17005
          | exact resolve b1e17005 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17005
        have b1e17669 : (σ x) ≠ (M.op x (σ y)) ∨ x = (k y y) := by
          first
          | (have i₁ := b1e221
             have i₂ := b1e17035
             grind)
          | exact superpose b1e17035 b1e221
          | exact resolve b1e221 b1e17035
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17035
        have b1e17743 : x = (k y y) := by
          first
          | (have r₁ := b1e17669
             have r₂ := b1e15971
             grind)
          | exact resolve b1e17669 b1e15971
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15971 b1e17669
        have b1e20800 : ∀ X0 : G, y ≠ (M.op X0 X0) ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e20
             have i₂ := b1e15765 X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e15765 x
             grind)
          | exact superpose b1e15765 b1e20
          | (have j1 := b1e15765 X0
             grind)
          | exact resolve b1e20 b1e15765
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e20896 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e537 X0 X0
             have i₂ := b1e15765 X0
             grind)
          | (have i₁ := b1e537 x x
             have i₂ := b1e15765 X0
             grind)
          | exact superpose b1e15765 b1e537
          | (have j0 := b1e537 X0 X0
             have j1 := b1e15765 X0
             grind)
          | (have r₁ := b1e537 (M.op x x) (M.op x x)
             have r₂ := b1e15765 (M.op x x)
             grind)
          | exact resolve b1e537 b1e15765
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e537 b1e15765
        have b1e20975 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e20896 X0
             have j1 := b1e15 X0 x
             grind)
          | (have r₁ := b1e20896 X0
             have r₂ := b1e15 X0 x
             grind)
          | (have r₁ := b1e20896 (M.op x x)
             have r₂ := b1e15 (M.op x x) x
             grind)
          | (have r₁ := b1e20896 (k x x)
             have r₂ := b1e15 x x
             grind)
          | exact resolve b1e20896 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e20896
        have b1e22553 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e20975 X0
             grind)
          | exact superpose b1e20975 b1e15
          | (have j0 := b1e15 X0 X0
             have j1 := b1e20975 X0
             grind)
          | exact resolve b1e15 b1e20975
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e20975
        have b1e22631 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e22553 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e22553
        have b1e23435 : ∀ X0 : G, y ≠ X0 ∨ (M.op x X0) = (k X0 x) ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e20800 X0
             have i₂ := b1e22631 X0
             grind)
          | exact superpose b1e22631 b1e20800
          | (have j0 := b1e20800 X0
             have j1 := b1e22631 X0
             grind)
          | (have r₁ := b1e20800 y
             have r₂ := b1e22631 y
             grind)
          | exact resolve b1e20800 b1e22631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e20800 b1e22631
        have b1e23528 : ∀ X0 : G, y ≠ X0 ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e23435 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23435
        have b1e24363 : (M.op x y) = (k y x) := by
          first
          | (have j0 := b1e23528 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23528
        have b1e24364 : (M.op y x) = (k y x) := by
          first
          | (have i₁ := b1e24363
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e24363
          | exact resolve b1e24363 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24363
        have b1e24640 : (M.op x (σ y)) = (σ (M.op y x)) ∨ (σ y) = (M.op x x) := by
          first
          | (have i₁ := b1e1871 y
             have i₂ := b1e24364
             grind)
          | exact superpose b1e24364 b1e1871
          | (have j0 := b1e1871 y
             grind)
          | exact resolve b1e1871 b1e24364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1871
        have b1e24667 : (σ y) = (M.op x x) := by
          first
          | (have r₁ := b1e24640
             have r₂ := b1e221
             grind)
          | exact resolve b1e24640 b1e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e221 b1e24640
        have b1e25357 : (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e859
             have i₂ := b1e24667
             grind)
          | exact superpose b1e24667 b1e859
          | exact resolve b1e859 b1e24667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e859
        have b1e25402 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e179 x
             have i₂ := b1e24667
             grind)
          | exact superpose b1e24667 b1e179
          | exact resolve b1e179 b1e24667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e179 b1e24667
        have b1e25423 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e25402
             have i₂ := b1e16 y y
             grind)
          | exact superpose b1e16 b1e25402
          | exact resolve b1e25402 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25402
        have b1e25444 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b1e25357
             have i₂ := b1e16 y x
             grind)
          | exact superpose b1e16 b1e25357
          | exact resolve b1e25357 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25357
        have b1e25447 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e25423
             have i₂ := b1e17743
             grind)
          | exact superpose b1e17743 b1e25423
          | exact resolve b1e25423 b1e17743
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17743 b1e25423
        have b1e25455 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e25444
             have i₂ := b1e24364
             grind)
          | exact superpose b1e24364 b1e25444
          | exact resolve b1e25444 b1e24364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24364 b1e25444
        have b1e25459 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e25455
             have i₂ := b1e25447
             grind)
          | exact superpose b1e25447 b1e25455
          | exact resolve b1e25455 b1e25447
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25455
        have b1e28448 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e25447
             grind)
          | exact superpose b1e25447 b1e17
          | exact resolve b1e17 b1e25447
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28567 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e28448
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e28448
          | exact resolve b1e28448 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28448
        have b1e28588 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e28567
             have i₂ := b1e25447
             grind)
          | exact superpose b1e25447 b1e28567
          | exact resolve b1e28567 b1e25447
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25447 b1e28567
        have b1e28604 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e28588
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e28588
          | exact resolve b1e28588 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e28588
        have b1e28617 : False := by grind
        exact b1e28617
    · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
      · have b2e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : x = (M.op y y) := by grind
        have b2e19 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e33 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 X0 X1 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11
          | exact resolve b2e11 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 X0 X1 y
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e11
          | exact resolve b2e11 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e19
             have i₂ := b2e15 X0 (σ y)
             grind)
          | (have i₁ := b2e19
             have i₂ := b2e15 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e15 b2e19
          | (have j1 := b2e15 X0 (σ y)
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e15 (σ x) (σ y)
             grind)
          | exact resolve b2e19 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e71 : y = (M.op x y) := by
          first
          | (have i₁ := b2e34 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e34
          | exact resolve b2e34 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e33 X0 x
             have i₂ := b2e34 X0 x
             grind)
          | exact superpose b2e34 b2e33
          | exact resolve b2e33 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e34
        have b2e85 : y = (M.op y y) := by
          first
          | (have i₁ := b2e71
             have i₂ := b2e76 y
             grind)
          | exact superpose b2e76 b2e71
          | exact resolve b2e71 b2e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71 b2e76
        have b2e107 : x = y := by
          first
          | (have i₁ := b2e18
             have i₂ := b2e85
             grind)
          | exact superpose b2e85 b2e18
          | exact resolve b2e18 b2e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e109 : y = (k y y) := by grind
        clear b2e85
        have b2e815 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e57 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e816 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b2e815
             have i₂ := b2e107
             grind)
          | exact superpose b2e107 b2e815
          | exact resolve b2e815 b2e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e815
        have b2e817 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b2e816
             have i₂ := b2e16 y y
             grind)
          | exact superpose b2e16 b2e816
          | exact resolve b2e816 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e816
        have b2e818 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e817
             have i₂ := b2e109
             grind)
          | exact superpose b2e109 b2e817
          | exact resolve b2e817 b2e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109 b2e817
        have b2e1117 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e818
             grind)
          | exact superpose b2e818 b2e19
          | exact resolve b2e19 b2e818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e818
        have b2e1145 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1117
             have i₂ := b2e107
             grind)
          | exact superpose b2e107 b2e1117
          | exact resolve b2e1117 b2e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e107 b2e1117
        have b2e1146 : False := by grind
        exact b2e1146
      · have b3e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          grind
        have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : x = (M.op y y) := by grind
        have b3e19 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e22 : y = (k x y) := by grind
        have b3e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 (τ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e16
          | exact resolve b3e16 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e11 X0 X1 y
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e11
          | exact resolve b3e11 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e49 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e19
             have i₂ := b3e15 X0 (σ y)
             grind)
          | (have i₁ := b3e19
             have i₂ := b3e15 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b3e15 b3e19
          | (have j1 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e15 (σ x) (σ y)
             grind)
          | exact resolve b3e19 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X1 X0
             have i₂ := b3e15 (σ X1) (σ X0)
             grind)
          | exact superpose b3e15 b3e16
          | (have j1 := b3e15 (σ X1) (σ X0)
             grind)
          | exact resolve b3e16 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (k (τ X0) X1)
             have i₂ := b3e23 X0 X1
             grind)
          | exact superpose b3e23 b3e12
          | exact resolve b3e12 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e427 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e46 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e435 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          grind
        clear b3e59
        have b3e441 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e435 X0
             have i₂ := b3e12 X0
             grind)
          | exact superpose b3e12 b3e435
          | exact resolve b3e435 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e435
        have b3e610 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b3e49 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e611 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e610
             have i₂ := b3e16 x y
             grind)
          | exact superpose b3e16 b3e610
          | exact resolve b3e610 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e610
        have b3e612 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e611
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e611
          | exact resolve b3e611 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22 b3e611
        have b3e615 : (M.op (σ y) (σ y)) = (M.op x (σ y)) := by
          first
          | (have i₁ := b3e28 (σ y) (σ x)
             have i₂ := b3e612
             grind)
          | exact superpose b3e612 b3e28
          | exact resolve b3e28 b3e612
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e612
        have b3e1078 : x ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b3e427 y y
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e427
          | (have j0 := b3e427 y y
             grind)
          | exact resolve b3e427 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e427
        have b3e1146 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e50 y y
             grind)
          | exact superpose b3e50 b3e19
          | (have j1 := b3e50 y y
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e50 y x
             grind)
          | exact resolve b3e19 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e1219 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op x (σ y)) := by
          first
          | (have i₁ := b3e1146
             have i₂ := b3e615
             grind)
          | exact superpose b3e615 b3e1146
          | exact resolve b3e1146 b3e615
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1146
        have b3e1464 : y = (k (τ (M.op x (σ y))) y) := by
          first
          | (have i₁ := b3e441 y
             have i₂ := b3e615
             grind)
          | exact superpose b3e615 b3e441
          | exact resolve b3e441 b3e615
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e441 b3e615
        have b3e1542 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e1219
             have i₂ := b3e15 y y
             grind)
          | exact superpose b3e15 b3e1219
          | (have j1 := b3e15 y y
             grind)
          | exact resolve b3e1219 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1219
        have b3e1558 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e1542
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e1542
          | exact resolve b3e1542 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1542
        have b3e1559 : (σ y) = (M.op x (σ y)) ∨ y = (M.op y y) := by grind
        clear b3e1558
        have b3e1560 : (σ y) = (M.op x (σ y)) ∨ x = y := by
          first
          | (have i₁ := b3e1559
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e1559
          | exact resolve b3e1559 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1559
        have b3e1681 : y = (k (τ (σ y)) y) ∨ x = y := by
          first
          | (have i₁ := b3e1464
             have i₂ := b3e1560
             grind)
          | exact superpose b3e1560 b3e1464
          | exact resolve b3e1464 b3e1560
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1464 b3e1560
        have b3e1700 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b3e1681
             have i₂ := b3e12 y
             grind)
          | exact superpose b3e12 b3e1681
          | exact resolve b3e1681 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1681
        have b3e1703 : y = (k y y) := by
          first
          | (have r₁ := b3e1700
             have r₂ := b3e1078
             grind)
          | exact resolve b3e1700 b3e1078
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1078 b3e1700
        have b3e1764 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e15 y y
             have i₂ := b3e1703
             grind)
          | exact superpose b3e1703 b3e15
          | (have j0 := b3e15 y y
             grind)
          | exact resolve b3e15 b3e1703
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1703
        have b3e1769 : y = (M.op y y) := by grind
        clear b3e1764
        have b3e1826 : x = y := by
          first
          | (have i₁ := b3e18
             have i₂ := b3e1769
             grind)
          | exact superpose b3e1769 b3e18
          | exact resolve b3e18 b3e1769
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1906 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e1826
             grind)
          | exact superpose b3e1826 b3e20
          | exact resolve b3e20 b3e1826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1826
        have b3e1925 : False := by grind
        exact b3e1925
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b4e18 : x ≠ (M.op y y) := by grind
        have b4e19 : (σ x) = (M.op (σ y) (σ y)) := by grind
        have b4e20 : y = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e23 : (σ y) = (k (σ x) (σ y)) := by grind
        have b4e24 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b4e23
             have i₂ := b4e16 x y
             grind)
          | exact superpose b4e16 b4e23
          | exact resolve b4e23 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e23
        have b4e29 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b4e12 (k x y)
             have i₂ := b4e24
             grind)
          | exact superpose b4e24 b4e12
          | exact resolve b4e12 b4e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e24
        have b4e30 : y = (k x y) := by
          first
          | (have i₁ := b4e29
             have i₂ := b4e12 y
             grind)
          | exact superpose b4e12 b4e29
          | exact resolve b4e29 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e29
        have b4e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b4e11 X0 X1 x
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b4e66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 X1 X0
             have i₂ := b4e15 (σ X1) (σ X0)
             grind)
          | exact superpose b4e15 b4e16
          | (have j1 := b4e15 (σ X1) (σ X0)
             grind)
          | exact resolve b4e16 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e67 : y = (M.op y x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b4e30
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e30
          | (have j1 := b4e15 x y
             grind)
          | exact resolve b4e30 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e30
        have b4e71 : y = (M.op y x) := by
          first
          | (have r₁ := b4e67
             have r₂ := b4e18
             grind)
          | exact resolve b4e67 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e67
        have b4e82 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b4e38 x x
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e38
          | exact resolve b4e38 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e38
        have b4e90 : y = (M.op x y) := by
          first
          | (have i₁ := b4e82
             have i₂ := b4e71
             grind)
          | exact superpose b4e71 b4e82
          | exact resolve b4e82 b4e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e71 b4e82
        have b4e1803 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e66 y y
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e66
          | exact resolve b4e66 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e66
        have b4e2407 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e12 (k y y)
             have i₂ := b4e1803
             grind)
          | exact superpose b4e1803 b4e12
          | exact resolve b4e12 b4e1803
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1803
        have b4e2421 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e2407
             have i₂ := b4e12 x
             grind)
          | exact superpose b4e12 b4e2407
          | exact resolve b4e2407 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2407
        have b4e2502 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b4e62 y y
             have i₂ := b4e2421
             grind)
          | exact superpose b4e2421 b4e62
          | exact resolve b4e62 b4e2421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e62 b4e2421
        have b4e2505 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b4e2502
             have r₂ := b4e18
             grind)
          | exact resolve b4e2502 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2502
        have b4e2564 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b4e12 x
             have i₂ := b4e2505
             grind)
          | exact superpose b4e2505 b4e12
          | exact resolve b4e12 b4e2505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2505
        have b4e2580 : x = y ∨ x = y := by
          first
          | (have i₁ := b4e2564
             have i₂ := b4e12 y
             grind)
          | exact superpose b4e12 b4e2564
          | exact resolve b4e2564 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2564
        have b4e2581 : x = y := by grind
        clear b4e2580
        have b4e2641 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b4e17
             have i₂ := b4e2581
             grind)
          | exact superpose b4e2581 b4e17
          | exact resolve b4e17 b4e2581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e2655 : y = (M.op y y) := by
          first
          | (have i₁ := b4e90
             have i₂ := b4e2581
             grind)
          | exact superpose b4e2581 b4e90
          | exact resolve b4e90 b4e2581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e90
        have b4e2667 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b4e2641
             have i₂ := b4e2655
             grind)
          | exact superpose b4e2655 b4e2641
          | exact resolve b4e2641 b4e2655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2641 b4e2655
        have b4e2670 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b4e2667
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e2667
          | exact resolve b4e2667 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2667
        have b4e2672 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b4e2670
             have i₂ := b4e2581
             grind)
          | exact superpose b4e2581 b4e2670
          | exact resolve b4e2670 b4e2581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2581 b4e2670
        have b4e2673 : False := by grind
        exact b4e2673
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : x ≠ (M.op y y) := by grind
        have b5e19 : (σ x) = (M.op (σ y) (σ y)) := by grind
        have b5e20 : y ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e22 : (σ y) = (k (σ x) (σ y)) := by grind
        have b5e23 : (σ y) = (σ (k x y)) := by
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
        have b5e24 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b5e12 (k x y)
             have i₂ := b5e23
             grind)
          | exact superpose b5e23 b5e12
          | exact resolve b5e12 b5e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e23
        have b5e25 : y = (k x y) := by
          first
          | (have i₁ := b5e24
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e24
          | exact resolve b5e24 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24
        have b5e58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b5e62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b5e16 X1 X0
             have i₂ := b5e15 (σ X1) (σ X0)
             grind)
          | exact superpose b5e15 b5e16
          | (have j1 := b5e15 (σ X1) (σ X0)
             grind)
          | exact resolve b5e16 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e64 : y = (M.op y x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b5e25
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e25
          | (have j1 := b5e15 x y
             grind)
          | exact resolve b5e25 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25
        have b5e67 : y = (M.op y x) := by
          first
          | (have r₁ := b5e64
             have r₂ := b5e18
             grind)
          | exact resolve b5e64 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e64
        have b5e1623 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e62 y y
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e62
          | exact resolve b5e62 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62
        have b5e2026 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e12 (k y y)
             have i₂ := b5e1623
             grind)
          | exact superpose b5e1623 b5e12
          | exact resolve b5e12 b5e1623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1623
        have b5e2039 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e2026
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e2026
          | exact resolve b5e2026 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2026
        have b5e2046 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b5e58 y y
             have i₂ := b5e2039
             grind)
          | exact superpose b5e2039 b5e58
          | exact resolve b5e58 b5e2039
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e58 b5e2039
        have b5e2049 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b5e2046
             have r₂ := b5e18
             grind)
          | exact resolve b5e2046 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2046
        have b5e2122 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b5e12 x
             have i₂ := b5e2049
             grind)
          | exact superpose b5e2049 b5e12
          | exact resolve b5e12 b5e2049
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2049
        have b5e2138 : x = y ∨ x = y := by
          first
          | (have i₁ := b5e2122
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e2122
          | exact resolve b5e2122 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e2122
        have b5e2139 : x = y := by grind
        clear b5e2138
        have b5e2177 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b5e20
             have i₂ := b5e2139
             grind)
          | exact superpose b5e2139 b5e20
          | exact resolve b5e20 b5e2139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e2182 : y = (M.op y y) := by
          first
          | (have i₁ := b5e67
             have i₂ := b5e2139
             grind)
          | exact superpose b5e2139 b5e67
          | exact resolve b5e67 b5e2139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e67 b5e2139
        have b5e2197 : False := by grind
        exact b5e2197
    · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
      · have b6e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          grind
        have b6e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : x ≠ (M.op y y) := by grind
        have b6e19 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b6e20 : y = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e22 : x = (k y x) := by grind
        have b6e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 (τ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e16
          | exact resolve b6e16 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 (τ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e16
          | exact resolve b6e16 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e11 X0 X1 x
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e11
          | exact resolve b6e11 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b6e28 x x
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e28
          | exact resolve b6e28 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b6e28 X0 (M.op X0 x)
             have i₂ := b6e28 X0 x
             grind)
          | exact superpose b6e28 b6e28
          | exact resolve b6e28 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = (M.op y (M.op X2 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e28 (M.op X2 X2) X0
             have i₂ := b6e11 X0 X1 X2
             grind)
          | exact superpose b6e11 b6e28
          | exact resolve b6e28 b6e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : ∀ X0 X2 : G, (M.op (M.op X2 X2) X0) = (M.op y X0) := by
          intro X0 X2
          first
          | (have i₁ := b6e11 X0 x X2
             have i₂ := b6e28 X0 x
             grind)
          | exact superpose b6e28 b6e11
          | exact resolve b6e11 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op y (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e34 X0 X1 X2
             have i₂ := b6e36 (M.op X0 (M.op X0 X1)) X2
             grind)
          | exact superpose b6e36 b6e34
          | exact resolve b6e34 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e40 : ∀ X0 X2 : G, (M.op y (M.op X2 X2)) = (M.op y (M.op y X0)) := by
          intro X0 X2
          first
          | (have i₁ := b6e38 X0 x X2
             have i₂ := b6e28 X0 x
             grind)
          | exact superpose b6e28 b6e38
          | exact resolve b6e38 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e41 : ∀ X2 : G, (M.op y y) = (M.op y (M.op X2 X2)) := by
          intro X2
          first
          | (have i₁ := b6e40 x X2
             have i₂ := b6e28 y x
             grind)
          | exact superpose b6e28 b6e40
          | exact resolve b6e40 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e45 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (k X0 X3) = (M.op X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e11 X1 X2 X3
             have i₂ := b6e15 X0 X3
             grind)
          | (have i₁ := b6e11 X0 X1 X2
             have i₂ := b6e15 (M.op X2 X2) X1
             grind)
          | exact superpose b6e15 b6e11
          | (have j1 := b6e15 X0 X3
             grind)
          | exact resolve b6e11 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e49 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e15 X0 (σ y)
             grind)
          | (have i₁ := b6e19
             have i₂ := b6e15 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b6e15 b6e19
          | (have j1 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e19
             have r₂ := b6e15 (σ x) (σ y)
             grind)
          | exact resolve b6e19 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e15 (σ X1) (σ X0)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 (σ X1) (σ X0)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y X1) ∨ (k X0 X3) = (M.op X3 X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e45 X0 X1 x X3
             have i₂ := b6e28 X1 x
             grind)
          | exact superpose b6e28 b6e45
          | (have j0 := b6e45 X0 X1 x X3
             grind)
          | exact resolve b6e45 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e56 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e23 X1 X0
             have i₂ := b6e15 (τ X1) X0
             grind)
          | exact superpose b6e15 b6e23
          | (have j1 := b6e15 (τ X1) X0
             grind)
          | exact resolve b6e23 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (k (τ X0) X1)
             have i₂ := b6e23 X0 X1
             grind)
          | exact superpose b6e23 b6e12
          | exact resolve b6e12 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e70 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
          intro X0
          grind
        have b6e75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (k X0 (τ X1))
             have i₂ := b6e24 X1 X0
             grind)
          | exact superpose b6e24 b6e12
          | exact resolve b6e12 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e78 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e70 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e70
          | exact resolve b6e70 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e418 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          grind
        have b6e424 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e418 X0
             have i₂ := b6e12 X0
             grind)
          | exact superpose b6e12 b6e418
          | exact resolve b6e418 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e418
        have b6e432 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e46 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e440 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e75 X1 X0
             have i₂ := b6e15 (σ X1) X0
             grind)
          | exact superpose b6e15 b6e75
          | (have j1 := b6e15 (σ X1) X0
             grind)
          | exact resolve b6e75 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e606 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e78 X1
             have i₂ := b6e15 X0 (τ X1)
             grind)
          | (have i₁ := b6e78 X0
             have i₂ := b6e15 (M.op (τ X0) (τ X0)) X1
             grind)
          | exact superpose b6e15 b6e78
          | (have j1 := b6e15 X0 (τ X1)
             grind)
          | exact resolve b6e78 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e626 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b6e49 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e627 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e626
             have i₂ := b6e16 x y
             grind)
          | exact superpose b6e16 b6e626
          | exact resolve b6e626 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e626
        have b6e630 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e432 (M.op X0 X1) X0
             have i₂ := b6e28 X0 X1
             grind)
          | exact superpose b6e28 b6e432
          | (have j0 := b6e432 (M.op X0 X1) X0
             grind)
          | exact resolve b6e432 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e638 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op y X0) ∨ (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e432 X0 (M.op X1 X1)
             have i₂ := b6e36 X0 X1
             grind)
          | exact superpose b6e36 b6e432
          | (have j0 := b6e432 X0 (M.op X1 X1)
             grind)
          | (have r₁ := b6e432 y (M.op y y)
             have r₂ := b6e36 y y
             grind)
          | exact resolve b6e432 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e432
        have b6e719 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op y X2) = (M.op (σ X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e16 X1 X0
             have i₂ := b6e53 (σ X1) X2 (σ X0)
             grind)
          | exact superpose b6e53 b6e16
          | (have j1 := b6e53 (σ X1) X2 x
             grind)
          | exact resolve b6e16 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e1072 : (M.op y (σ y)) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e28 (σ y) (σ x)
             have i₂ := b6e627
             grind)
          | exact superpose b6e627 b6e28
          | exact resolve b6e28 b6e627
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1168 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op y (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 (σ X1) (σ X0)
             have i₂ := b6e50 X1 X0
             grind)
          | exact superpose b6e50 b6e28
          | (have j1 := b6e50 X1 X0
             grind)
          | exact resolve b6e28 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op y y) = (M.op y (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e41 (σ X1)
             have i₂ := b6e50 X1 X0
             grind)
          | exact superpose b6e50 b6e41
          | (have j1 := b6e50 X1 X0
             grind)
          | exact resolve b6e41 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op y (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 (σ X1) (σ X1)
             have i₂ := b6e50 X1 X0
             grind)
          | exact superpose b6e50 b6e28
          | (have j1 := b6e50 X1 X0
             grind)
          | exact resolve b6e28 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1197 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e50 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1245 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e424 X1
             have i₂ := b6e50 X1 X0
             grind)
          | exact superpose b6e50 b6e424
          | (have j1 := b6e50 X1 X0
             grind)
          | exact resolve b6e424 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e1267 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e1245 X0 X1
             have i₂ := b6e12 X0
             grind)
          | exact superpose b6e12 b6e1245
          | (have j0 := b6e1245 X0 X1
             grind)
          | exact resolve b6e1245 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1245
        have b6e1607 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op (M.op y y) X0) (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b6e630 (M.op y y) X0
             have i₂ := b6e32 y
             grind)
          | exact superpose b6e32 b6e630
          | (have j0 := b6e630 (M.op y y) X0
             grind)
          | (have r₁ := b6e630 (M.op y y) x
             have r₂ := b6e32 y
             grind)
          | exact resolve b6e630 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e630
        have b6e1609 : ∀ X0 : G, (M.op y y) = (k (M.op (M.op y y) X0) (M.op y y)) := by
          intro X0
          first
          | (have j0 := b6e1607 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1607
        have b6e1611 : ∀ X0 : G, (M.op y y) = (k (M.op y X0) (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b6e1609 X0
             have i₂ := b6e36 X0 y
             grind)
          | exact superpose b6e36 b6e1609
          | exact resolve b6e1609 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1609
        have b6e2045 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b6e1197 (M.op y y)
             have i₂ := b6e1611 y
             grind)
          | exact superpose b6e1611 b6e1197
          | (have j0 := b6e1197 (M.op y y)
             grind)
          | exact resolve b6e1197 b6e1611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1611
        have b6e2049 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e1197 (τ X0)
             have i₂ := b6e24 X0 (τ X0)
             grind)
          | exact superpose b6e24 b6e1197
          | (have j0 := b6e1197 (τ X0)
             grind)
          | exact resolve b6e1197 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e2051 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
        clear b6e2045
        have b6e2053 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e2049 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e2049
          | (have j0 := b6e2049 X0
             grind)
          | exact resolve b6e2049 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2049
        have b6e2057 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e2053 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e2053
          | (have j0 := b6e2053 X0
             grind)
          | exact resolve b6e2053 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2053
        have b6e2099 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e56 X0 (σ X0)
             have i₂ := b6e12 X0
             grind)
          | exact superpose b6e12 b6e56
          | exact resolve b6e56 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2155 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 X1
             have i₂ := b6e56 X0 X1
             grind)
          | exact superpose b6e56 b6e13
          | (have j1 := b6e56 X0 X1
             grind)
          | exact resolve b6e13 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e2201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e2099 X0 X1
             have i₂ := b6e16 X0 X1
             grind)
          | exact superpose b6e16 b6e2099
          | (have j0 := b6e2099 X0 X1
             grind)
          | exact resolve b6e2099 b6e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2099
        have b6e3934 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
          intro X0
          first
          | (have i₁ := b6e36 X0 (σ (M.op y y))
             have i₂ := b6e2051
             grind)
          | exact superpose b6e2051 b6e36
          | exact resolve b6e36 b6e2051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3936 : (M.op y y) = (M.op y (σ (M.op y y))) := by
          first
          | (have i₁ := b6e41 (σ (M.op y y))
             have i₂ := b6e2051
             grind)
          | exact superpose b6e2051 b6e41
          | exact resolve b6e41 b6e2051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e3942 : (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op y (σ (M.op y y))) := by
          first
          | (have i₁ := b6e28 (σ (M.op y y)) (σ (M.op y y))
             have i₂ := b6e2051
             grind)
          | exact superpose b6e2051 b6e28
          | exact resolve b6e28 b6e2051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3953 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
          first
          | (have i₁ := b6e3942
             have i₂ := b6e2051
             grind)
          | exact superpose b6e2051 b6e3942
          | exact resolve b6e3942 b6e2051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2051 b6e3942
        have b6e3970 : (M.op y y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e3953
             have i₂ := b6e3936
             grind)
          | exact superpose b6e3936 b6e3953
          | exact resolve b6e3953 b6e3936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3953
        have b6e4921 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e17
             have i₂ := b6e719 X0 x (σ y)
             grind)
          | exact superpose b6e719 b6e17
          | (have j1 := b6e719 X0 x x
             grind)
          | exact resolve b6e17 b6e719
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e719
        have b6e4978 : ∀ X0 : G, (M.op y (σ y)) ≠ (σ (M.op y x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e4921 X0
             have i₂ := b6e31
             grind)
          | exact superpose b6e31 b6e4921
          | (have j0 := b6e4921 X0
             grind)
          | exact resolve b6e4921 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4921
        have b6e7112 : (M.op y (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e1168 y x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1168
          | (have j0 := b6e1168 y x
             grind)
          | exact resolve b6e1168 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22 b6e1168
        have b6e7332 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op y (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op y (σ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e1195 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1195
        have b6e17499 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
          intro X0
          first
          | (have i₁ := b6e2057 (σ X0)
             have i₂ := b6e606 X0 (σ X0)
             grind)
          | exact superpose b6e606 b6e2057
          | (have j0 := b6e2057 (σ X0)
             have j1 := b6e606 X0 (σ X0)
             grind)
          | (have r₁ := b6e2057 (σ X0)
             have r₂ := b6e606 X0 (σ X0)
             grind)
          | exact resolve b6e2057 b6e606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e606 b6e2057
        have b6e17547 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
          intro X0
          first
          | (have j0 := b6e17499 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17499
        have b6e17568 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b6e17547 X0
             have i₂ := b6e12 X0
             grind)
          | exact superpose b6e12 b6e17547
          | (have j0 := b6e17547 X0
             grind)
          | exact resolve b6e17547 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17547
        have b6e24316 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e424 X1
             have i₂ := b6e440 (σ X1) X0
             grind)
          | exact superpose b6e440 b6e424
          | (have j1 := b6e440 (σ X1) X0
             grind)
          | exact resolve b6e424 b6e440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e424 b6e440
        have b6e24401 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e24316 X0 X1
             have i₂ := b6e12 X0
             grind)
          | exact superpose b6e12 b6e24316
          | (have j0 := b6e24316 X0 X1
             grind)
          | exact resolve b6e24316 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24316
        have b6e24574 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e24401 X0 X1
             have i₂ := b6e12 X1
             grind)
          | exact superpose b6e12 b6e24401
          | (have j0 := b6e24401 X0 X1
             grind)
          | exact resolve b6e24401 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24401
        have b6e24880 : (M.op y y) = (k y (M.op y y)) := by
          first
          | (have j0 := b6e638 y y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e638
        have b6e27024 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (σ (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op X1 (τ X0))
             have i₂ := b6e2155 X1 X0
             grind)
          | exact superpose b6e2155 b6e12
          | (have j1 := b6e2155 X1 X0
             grind)
          | exact resolve b6e12 b6e2155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2155
        have b6e27132 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (σ (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e27024 X0 X1
             have i₂ := b6e59 X0 X1
             grind)
          | exact superpose b6e59 b6e27024
          | (have j0 := b6e27024 X0 X1
             grind)
          | exact resolve b6e27024 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e27024
        have b6e43306 : (σ y) ≠ (M.op y (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
        have b6e62719 : (σ (M.op y y)) ≠ (M.op y (σ (M.op y y))) ∨ (M.op y (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have i₁ := b6e7332 (M.op y y) y
             have i₂ := b6e24880
             grind)
          | exact superpose b6e24880 b6e7332
          | (have j0 := b6e7332 (M.op y y) y
             grind)
          | exact resolve b6e7332 b6e24880
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7332 b6e24880
        have b6e62769 : (M.op y y) ≠ (σ (M.op y y)) ∨ (M.op y (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have i₁ := b6e62719
             have i₂ := b6e3936
             grind)
          | exact superpose b6e3936 b6e62719
          | exact resolve b6e62719 b6e3936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62719
        have b6e62811 : (M.op y (σ (M.op y y))) = (M.op (σ (M.op y y)) (σ y)) := by
          first
          | (have r₁ := b6e62769
             have r₂ := b6e3970
             grind)
          | exact resolve b6e62769 b6e3970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62769
        have b6e62839 : (M.op y (σ y)) = (M.op y (σ (M.op y y))) := by
          first
          | (have i₁ := b6e62811
             have i₂ := b6e3934 (σ y)
             grind)
          | exact superpose b6e3934 b6e62811
          | exact resolve b6e62811 b6e3934
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3934 b6e62811
        have b6e62860 : (M.op y y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b6e62839
             have i₂ := b6e3936
             grind)
          | exact superpose b6e3936 b6e62839
          | exact resolve b6e62839 b6e3936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3936 b6e62839
        have b6e71134 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (k X0 X0)) X1) ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e36 X1 (σ X0)
             have i₂ := b6e1267 X0 X0
             grind)
          | exact superpose b6e1267 b6e36
          | (have j1 := b6e1267 X0 X0
             grind)
          | exact resolve b6e36 b6e1267
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1267
        have b6e73132 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e36 X1 (σ X0)
             have i₂ := b6e17568 X0
             grind)
          | exact superpose b6e17568 b6e36
          | (have j1 := b6e17568 X0
             grind)
          | exact resolve b6e36 b6e17568
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e73990 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (σ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e27132 (σ X0) X1
             have i₂ := b6e12 X0
             grind)
          | exact superpose b6e12 b6e27132
          | (have j0 := b6e27132 (σ X0) X1
             grind)
          | exact resolve b6e27132 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27132
        have b6e74259 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e73990 X0 x
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e73990
          | (have j0 := b6e73990 X0 x
             grind)
          | exact resolve b6e73990 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73990
        have b6e77838 : ∀ X0 : G, (σ X0) = (M.op y (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b6e17568 X0
             have i₂ := b6e73132 X0 (σ X0)
             grind)
          | exact superpose b6e73132 b6e17568
          | (have j0 := b6e17568 X0
             have j1 := b6e73132 X0 x
             grind)
          | exact resolve b6e17568 b6e73132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17568 b6e73132
        have b6e77950 : ∀ X0 : G, (σ X0) = (M.op y (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e77838 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77838
        have b6e78109 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (k x x) := by
          first
          | (have i₁ := b6e43306
             have i₂ := b6e77950 x
             grind)
          | exact superpose b6e77950 b6e43306
          | (have j1 := b6e77950 x
             grind)
          | exact resolve b6e43306 b6e77950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77950
        have b6e78246 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (k x x) := by
          first
          | (have j1 := b6e74259 x
             grind)
          | (have r₁ := b6e78109
             have r₂ := b6e74259 x
             grind)
          | exact resolve b6e78109 b6e74259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74259 b6e78109
        have b6e78253 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by
          first
          | (have i₁ := b6e78246
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e78246
          | exact resolve b6e78246 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78246
        have b6e78313 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b6e24574 x x
             have i₂ := b6e78253
             grind)
          | exact superpose b6e78253 b6e24574
          | (have j0 := b6e24574 x x
             grind)
          | exact resolve b6e24574 b6e78253
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24574 b6e78253
        have b6e78440 : y = (k x x) ∨ x = (k x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b6e78313
             have i₂ := b6e12 y
             grind)
          | exact superpose b6e12 b6e78313
          | exact resolve b6e78313 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78313
        have b6e78441 : x = (k x x) ∨ y = (k x x) := by grind
        clear b6e78440
        have b6e78576 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b6e15 x x
             have i₂ := b6e78441
             grind)
          | exact superpose b6e78441 b6e15
          | (have j0 := b6e15 x x
             grind)
          | exact resolve b6e15 b6e78441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e78594 : x ≠ y ∨ y = (k x x) := by grind
        clear b6e78441
        have b6e78595 : x = (M.op x x) ∨ y = (k x x) := by grind
        clear b6e78576
        have b6e78621 : x = y ∨ y = (k x x) := by
          first
          | (have i₁ := b6e78595
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e78595
          | exact resolve b6e78595 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78595
        have b6e78663 : y = (k x x) := by
          first
          | (have r₁ := b6e78621
             have r₂ := b6e78594
             grind)
          | exact resolve b6e78621 b6e78594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78594 b6e78621
        have b6e78733 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e1197 x
             have i₂ := b6e78663
             grind)
          | exact superpose b6e78663 b6e1197
          | (have j0 := b6e1197 x
             grind)
          | exact resolve b6e1197 b6e78663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1197
        have b6e78784 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b6e71134 x x
             have i₂ := b6e78663
             grind)
          | exact superpose b6e78663 b6e71134
          | exact resolve b6e71134 b6e78663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71134
        have b6e79098 : (σ (k x y)) = (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b6e627
             have i₂ := b6e78784 (σ x)
             grind)
          | exact superpose b6e78784 b6e627
          | exact resolve b6e627 b6e78784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e627 b6e78784
        have b6e80174 : (σ (M.op y x)) = (M.op y (σ x)) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b6e2201 x y
             have i₂ := b6e79098
             grind)
          | exact superpose b6e79098 b6e2201
          | (have j0 := b6e2201 x y
             grind)
          | exact resolve b6e2201 b6e79098
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2201 b6e79098
        have b6e80224 : (σ (M.op y x)) = (M.op y (σ x)) ∨ x = y := by
          first
          | (have r₁ := b6e80174
             have r₂ := b6e18
             grind)
          | exact resolve b6e80174 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80174
        have b6e80560 : ∀ X0 : G, (M.op y (σ y)) ≠ (M.op y (σ x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b6e4978 X0
             have i₂ := b6e80224
             grind)
          | exact superpose b6e80224 b6e4978
          | (have j0 := b6e4978 X0
             grind)
          | exact resolve b6e4978 b6e80224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4978
        have b6e80608 : ∀ X0 : G, (M.op y y) ≠ (M.op y (σ x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b6e80560 X0
             have i₂ := b6e62860
             grind)
          | exact superpose b6e62860 b6e80560
          | (have j0 := b6e80560 X0
             grind)
          | exact resolve b6e80560 b6e62860
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80560
        have b6e80612 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b6e80608 X0
             have j1 := b6e1190 x X0
             grind)
          | (have r₁ := b6e80608 X0
             have r₂ := b6e1190 x x
             grind)
          | exact resolve b6e80608 b6e1190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1190 b6e80608
        have b6e85874 : (M.op y (σ x)) = (σ (k x x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e80612 x
             have i₂ := b6e7112
             grind)
          | exact superpose b6e7112 b6e80612
          | exact resolve b6e80612 b6e7112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7112 b6e80612
        have b6e86041 : (σ y) = (M.op y (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e85874
             have i₂ := b6e78663
             grind)
          | exact superpose b6e78663 b6e85874
          | exact resolve b6e85874 b6e78663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85874
        have b6e86077 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have r₁ := b6e86041
             have r₂ := b6e43306
             grind)
          | exact resolve b6e86041 b6e43306
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43306 b6e86041
        have b6e86226 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b6e28 (σ x) (σ x)
             have i₂ := b6e86077
             grind)
          | exact superpose b6e86077 b6e28
          | exact resolve b6e28 b6e86077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e86077
        have b6e88592 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e86226
             grind)
          | exact superpose b6e86226 b6e17
          | exact resolve b6e17 b6e86226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86226
        have b6e88630 : (σ (M.op y x)) ≠ (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b6e88592
             have i₂ := b6e31
             grind)
          | exact superpose b6e31 b6e88592
          | exact resolve b6e88592 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31 b6e88592
        have b6e88637 : x = y := by
          first
          | (have r₁ := b6e88630
             have r₂ := b6e80224
             grind)
          | exact resolve b6e88630 b6e80224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80224 b6e88630
        have b6e88664 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e88637
             grind)
          | exact superpose b6e88637 b6e17
          | exact resolve b6e17 b6e88637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e88665 : y = (M.op y y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e88637
             grind)
          | exact superpose b6e88637 b6e20
          | exact resolve b6e20 b6e88637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e88671 : (M.op y (σ y)) = (M.op (σ y) (σ (k y y))) := by
          first
          | (have i₁ := b6e1072
             have i₂ := b6e88637
             grind)
          | exact superpose b6e88637 b6e1072
          | exact resolve b6e1072 b6e88637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1072
        have b6e88729 : y = (k y y) := by
          first
          | (have i₁ := b6e78663
             have i₂ := b6e88637
             grind)
          | exact superpose b6e88637 b6e78663
          | exact resolve b6e78663 b6e88637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78663
        have b6e88730 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e78733
             have i₂ := b6e88637
             grind)
          | exact superpose b6e88637 b6e78733
          | exact resolve b6e78733 b6e88637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78733 b6e88637
        have b6e88735 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e88730
        have b6e88759 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
          first
          | (have i₁ := b6e88671
             have i₂ := b6e88729
             grind)
          | exact superpose b6e88729 b6e88671
          | exact resolve b6e88671 b6e88729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88671 b6e88729
        have b6e88762 : (M.op y y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e88664
             have i₂ := b6e3970
             grind)
          | exact superpose b6e3970 b6e88664
          | exact resolve b6e88664 b6e3970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3970 b6e88664
        have b6e88773 : (M.op y y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e88759
             have i₂ := b6e62860
             grind)
          | exact superpose b6e62860 b6e88759
          | exact resolve b6e88759 b6e62860
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62860 b6e88759
        have b6e88775 : (σ y) ≠ (M.op y y) := by
          first
          | (have i₁ := b6e88762
             have i₂ := b6e88735
             grind)
          | exact superpose b6e88735 b6e88762
          | exact resolve b6e88762 b6e88735
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88762
        have b6e88778 : (σ y) = (M.op y y) := by
          first
          | (have i₁ := b6e88773
             have i₂ := b6e88735
             grind)
          | exact superpose b6e88735 b6e88773
          | exact resolve b6e88773 b6e88735
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88735 b6e88773
        have b6e88779 : y ≠ (σ y) := by
          first
          | (have i₁ := b6e88775
             have i₂ := b6e88665
             grind)
          | exact superpose b6e88665 b6e88775
          | exact resolve b6e88775 b6e88665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88775
        have b6e88781 : y = (σ y) := by
          first
          | (have i₁ := b6e88778
             have i₂ := b6e88665
             grind)
          | exact superpose b6e88665 b6e88778
          | exact resolve b6e88778 b6e88665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88665 b6e88778
        have b6e88782 : False := by grind
        exact b6e88782
      · have b7e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          grind
        have b7e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b7e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b7e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b7e15 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : x ≠ (M.op y y) := by grind
        have b7e19 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b7e20 : y ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 (τ X0) X1
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e16
          | exact resolve b7e16 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X1 (τ X0)
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e16
          | exact resolve b7e16 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b7e12 (k (τ X0) X1)
             have i₂ := b7e22 X0 X1
             grind)
          | exact superpose b7e22 b7e12
          | exact resolve b7e12 b7e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e33 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
          intro X0
          grind
        clear b7e23
        have b7e41 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e33 X0
             have i₂ := b7e13 X0
             grind)
          | exact superpose b7e13 b7e33
          | exact resolve b7e33 b7e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e33
        have b7e44 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (k X0 X3) = (M.op X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e11 X1 X2 X3
             have i₂ := b7e15 X0 X3
             grind)
          | (have i₁ := b7e11 X0 X1 X2
             have i₂ := b7e15 (M.op X2 X2) X1
             grind)
          | exact superpose b7e15 b7e11
          | (have j1 := b7e15 X0 X3
             grind)
          | exact resolve b7e11 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e47 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b7e19
             have i₂ := b7e15 X0 (σ y)
             grind)
          | (have i₁ := b7e19
             have i₂ := b7e15 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b7e15 b7e19
          | (have j1 := b7e15 X0 (σ y)
             grind)
          | (have r₁ := b7e19
             have r₂ := b7e15 (σ x) (σ y)
             grind)
          | exact resolve b7e19 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e49 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X1 X0
             have i₂ := b7e15 (σ X1) (σ X0)
             grind)
          | exact superpose b7e15 b7e16
          | (have j1 := b7e15 (σ X1) (σ X0)
             grind)
          | exact resolve b7e16 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e50 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e22 X1 X0
             have i₂ := b7e15 (τ X1) X0
             grind)
          | exact superpose b7e15 b7e22
          | (have j1 := b7e15 (τ X1) X0
             grind)
          | exact resolve b7e22 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e22
        have b7e54 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          grind
        clear b7e27
        have b7e61 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b7e54 X0
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e54
          | exact resolve b7e54 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e54
        have b7e138 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e41 X1
             have i₂ := b7e15 X0 (τ X1)
             grind)
          | (have i₁ := b7e41 X0
             have i₂ := b7e15 (M.op (τ X0) (τ X0)) X1
             grind)
          | exact superpose b7e15 b7e41
          | (have j1 := b7e15 X0 (τ X1)
             grind)
          | exact resolve b7e41 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e41
        have b7e231 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b7e47 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e47
        have b7e232 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e231
             have i₂ := b7e16 x y
             grind)
          | exact superpose b7e16 b7e231
          | exact resolve b7e231 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e231
        have b7e289 : ∀ X0 X1 X2 X3 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (M.op X2 X3)) = (M.op (σ X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b7e16 X1 X0
             have i₂ := b7e44 (σ X1) X2 X3 (σ X0)
             grind)
          | exact superpose b7e44 b7e16
          | (have j1 := b7e44 (σ X1) X2 X3 X3
             grind)
          | exact resolve b7e16 b7e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e44
        have b7e726 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e49 X0 X0
             have i₂ := b7e49 X0 X1
             grind)
          | exact superpose b7e49 b7e49
          | (have j0 := b7e49 X1 X0
             have j1 := b7e49 X1 X0
             grind)
          | exact resolve b7e49 b7e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e779 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e61 X1
             have i₂ := b7e49 X1 X0
             grind)
          | exact superpose b7e49 b7e61
          | (have j1 := b7e49 X1 X0
             grind)
          | exact resolve b7e61 b7e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e49 b7e61
        have b7e806 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b7e779 X0 X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e779
          | (have j0 := b7e779 X0 X1
             grind)
          | exact resolve b7e779 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e779
        have b7e1805 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e50 X0 (σ X0)
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e50
          | exact resolve b7e50 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e50
        have b7e1913 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b7e1805 X0 X1
             have i₂ := b7e16 X0 X1
             grind)
          | exact superpose b7e16 b7e1805
          | (have j0 := b7e1805 X0 X1
             grind)
          | exact resolve b7e1805 b7e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1805
        have b7e2241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b7e5447 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X1 X0
             have i₂ := b7e138 X1 (σ X0)
             grind)
          | exact superpose b7e138 b7e16
          | (have j1 := b7e138 X1 (σ X0)
             grind)
          | exact resolve b7e16 b7e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e138
        have b7e5487 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e5447 X0 X1
             have i₂ := b7e12 X0
             grind)
          | exact superpose b7e12 b7e5447
          | (have j0 := b7e5447 X0 X1
             grind)
          | exact resolve b7e5447 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e5447
        have b7e13120 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e806 y x
             grind)
          | exact superpose b7e806 b7e17
          | (have j1 := b7e806 y x
             grind)
          | exact resolve b7e17 b7e806
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e806
        have b7e13227 : x = (k y x) := by
          first
          | (have j1 := b7e2241 y x
             grind)
          | (have r₁ := b7e13120
             have r₂ := b7e2241 y x
             grind)
          | exact resolve b7e13120 b7e2241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e2241 b7e13120
        have b7e13592 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b7e1913 y x
             have i₂ := b7e13227
             grind)
          | exact superpose b7e13227 b7e1913
          | (have j0 := b7e1913 y x
             grind)
          | exact resolve b7e1913 b7e13227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e13593 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b7e13592
             have r₂ := b7e20
             grind)
          | exact resolve b7e13592 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13592
        have b7e18420 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (M.op X0 X1)) = (M.op (σ y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e17
             have i₂ := b7e289 x y X0 X1
             grind)
          | exact superpose b7e289 b7e17
          | (have j1 := b7e289 X0 y X0 X1
             grind)
          | exact resolve b7e17 b7e289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e289
        have b7e18741 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (M.op X0 X1)) = (M.op (σ y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b7e18420 X0 X1
             have i₂ := b7e13227
             grind)
          | exact superpose b7e13227 b7e18420
          | (have j0 := b7e18420 X0 X1
             grind)
          | exact resolve b7e18420 b7e13227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18420
        have b7e18763 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X0) := by
          intro X0 X1
          first
          | (have j0 := b7e18741 X0 X1
             grind)
          | (have r₁ := b7e18741 X0 X1
             have r₂ := b7e13593
             grind)
          | exact resolve b7e18741 b7e13593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18741
        have b7e18779 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b7e18763 X0 (M.op X0 x)
             have i₂ := b7e18763 X0 x
             grind)
          | exact superpose b7e18763 b7e18763
          | exact resolve b7e18763 b7e18763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e28114 : (σ (k x y)) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b7e18779 (σ x)
             have i₂ := b7e232
             grind)
          | exact superpose b7e232 b7e18779
          | exact resolve b7e18779 b7e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e232 b7e18779
        have b7e38323 : (σ (M.op y x)) = (M.op (σ x) (σ (M.op y x))) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b7e28114
             have i₂ := b7e1913 x y
             grind)
          | exact superpose b7e1913 b7e28114
          | (have j1 := b7e1913 x y
             grind)
          | exact resolve b7e28114 b7e1913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e1913 b7e28114
        have b7e38408 : (σ (M.op y x)) = (M.op (σ x) (σ (M.op y x))) := by
          first
          | (have r₁ := b7e38323
             have r₂ := b7e18
             grind)
          | exact resolve b7e38323 b7e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e38323
        have b7e42652 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op y x))) := by
          first
          | (have i₁ := b7e18763 (σ x) (σ (M.op y x))
             have i₂ := b7e38408
             grind)
          | exact superpose b7e38408 b7e18763
          | exact resolve b7e18763 b7e38408
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e18763
        have b7e42653 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b7e42652
             have i₂ := b7e38408
             grind)
          | exact superpose b7e38408 b7e42652
          | exact resolve b7e42652 b7e38408
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e38408 b7e42652
        have b7e85691 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e726 y x
             grind)
          | exact superpose b7e726 b7e17
          | (have j1 := b7e726 y x
             grind)
          | exact resolve b7e17 b7e726
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e726
        have b7e86007 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b7e85691
             have i₂ := b7e13227
             grind)
          | exact superpose b7e13227 b7e85691
          | exact resolve b7e85691 b7e13227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13227 b7e85691
        have b7e86117 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b7e86007
             have r₂ := b7e13593
             grind)
          | exact resolve b7e86007 b7e13593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e13593 b7e86007
        have b7e86226 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b7e12 (k x x)
             have i₂ := b7e86117
             grind)
          | exact superpose b7e86117 b7e12
          | exact resolve b7e12 b7e86117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e86117
        have b7e86284 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b7e86226
             have i₂ := b7e12 y
             grind)
          | exact superpose b7e12 b7e86226
          | exact resolve b7e86226 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e86226
        have b7e87026 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b7e5487 x x
             have i₂ := b7e86284
             grind)
          | exact superpose b7e86284 b7e5487
          | exact resolve b7e5487 b7e86284
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e5487 b7e86284
        have b7e87028 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
        clear b7e87026
        have b7e87031 : (σ x) = (σ y) := by
          first
          | (have r₁ := b7e87028
             have r₂ := b7e20
             grind)
          | exact resolve b7e87028 b7e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e87028
        have b7e87760 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e87031
             grind)
          | exact superpose b7e87031 b7e17
          | exact resolve b7e17 b7e87031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e87766 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b7e42653
             have i₂ := b7e87031
             grind)
          | exact superpose b7e87031 b7e42653
          | exact resolve b7e42653 b7e87031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e42653
        have b7e87767 : x = (τ (σ y)) := by
          first
          | (have i₁ := b7e12 x
             have i₂ := b7e87031
             grind)
          | exact superpose b7e87031 b7e12
          | exact resolve b7e12 b7e87031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e87031
        have b7e87828 : x = y := by
          first
          | (have i₁ := b7e87767
             have i₂ := b7e12 y
             grind)
          | exact superpose b7e12 b7e87767
          | exact resolve b7e87767 b7e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e87767
        have b7e87831 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b7e87760
             have i₂ := b7e87766
             grind)
          | exact superpose b7e87766 b7e87760
          | exact resolve b7e87760 b7e87766
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e87760 b7e87766
        have b7e87834 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b7e87831
             have i₂ := b7e87828
             grind)
          | exact superpose b7e87828 b7e87831
          | exact resolve b7e87831 b7e87828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e87828 b7e87831
        have b7e87835 : False := by grind
        exact b7e87835
