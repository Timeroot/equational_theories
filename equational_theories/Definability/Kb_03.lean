import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4424`: `x ◇ (x ◇ y) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4424 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4424 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4424.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X1) := by
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
      have b0e33 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
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
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
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
      have b0e38 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
        intro X1
        first
        | (have i₁ := b0e33 x X1
           have i₂ := b0e34 x X1
           grind)
        | exact superpose b0e34 b0e33
        | exact resolve b0e33 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e45 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e38 (σ y)
           grind)
        | exact superpose b0e38 b0e18
        | exact resolve b0e18 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e60 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X0
           have i₂ := b0e14 X3 X0
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X3 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
      have b0e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
      have b0e68 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e61 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e70 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op y X2) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e60 X0 x X2 X3
           have i₂ := b0e34 x X2
           grind)
        | exact superpose b0e34 b0e60
        | (have j0 := b0e60 X0 x X2 X3
           grind)
        | exact resolve b0e60 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e83 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X2 X2) X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 x X0 X2
           have i₂ := b0e34 x X0
           grind)
        | exact superpose b0e34 b0e10
        | exact resolve b0e10 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e113 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
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
      have b0e131 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e580 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e68 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e68 b0e15
        | (have j1 := b0e68 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e961 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e70 (σ x) (σ y) X0
           grind)
        | exact superpose b0e70 b0e16
        | (have j1 := b0e70 (σ x) x X0
           grind)
        | exact resolve b0e16 b0e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e988 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e961 X0
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e961
        | (have j0 := b0e961 X0
           grind)
        | exact resolve b0e961 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e961
      have b0e2773 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 X1 (σ X0)
           have i₂ := b0e65 X0 X0
           grind)
        | exact superpose b0e65 b0e13
        | (have j0 := b0e13 X1 (σ X0)
           have j1 := b0e65 X0 X1
           grind)
        | (have r₁ := b0e13 X0 (σ X0)
           have r₂ := b0e65 X0 X1
           grind)
        | exact resolve b0e13 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2820 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e65 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e65
      have b0e2849 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e2773 X0 X1
           have j1 := b0e13 X1 (σ X0)
           grind)
        | (have r₁ := b0e2773 X0 X1
           have r₂ := b0e13 X0 (σ X0)
           grind)
        | exact resolve b0e2773 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2773
      have b0e5359 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e113 X1 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e113
        | (have j0 := b0e113 X1 X1
           grind)
        | exact resolve b0e113 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113
      have b0e5508 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e5359 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e5359
        | (have j0 := b0e5359 X0 X1
           grind)
        | exact resolve b0e5359 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5359
      have b0e7569 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e2820 (τ X0)
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e2820
        | (have j0 := b0e2820 (τ X0)
           grind)
        | exact resolve b0e2820 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e2820
      have b0e7595 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e7569 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e7569
        | (have j0 := b0e7569 X0
           grind)
        | exact resolve b0e7569 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7569
      have b0e7610 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e7595 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e7595
        | (have j0 := b0e7595 X0
           grind)
        | exact resolve b0e7595 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7595
      have b0e8762 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e580 x y X0
           grind)
        | exact superpose b0e580 b0e16
        | (have j1 := b0e580 x x X0
           grind)
        | exact resolve b0e16 b0e580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e580
      have b0e60591 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e8762 X0
           have i₂ := b0e5508 y x
           grind)
        | exact superpose b0e5508 b0e8762
        | (have j0 := b0e8762 X0
           have j1 := b0e5508 X0 x
           grind)
        | (have r₁ := b0e8762 X0
           have r₂ := b0e5508 y x
           grind)
        | exact resolve b0e8762 b0e5508
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5508 b0e8762
      have b0e60593 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e60591 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60591
      have b0e60709 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e131 X0 (σ x)
           have i₂ := b0e60593 (σ X0)
           grind)
        | exact superpose b0e60593 b0e131
        | exact resolve b0e131 b0e60593
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e131 b0e60593
      have b0e60737 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e60709 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e60709
        | exact resolve b0e60709 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60709
      have b0e60754 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e60737 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e60737
        | exact resolve b0e60737 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60737
      have b0e60761 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e60754 X0
           have j1 := b0e13 X0 x
           grind)
        | (have r₁ := b0e60754 X0
           have r₂ := b0e13 X0 x
           grind)
        | exact resolve b0e60754 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60754
      have b0e61226 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2849 x X0
           have i₂ := b0e60761 x
           grind)
        | exact superpose b0e60761 b0e2849
        | (have j0 := b0e2849 x X0
           grind)
        | exact resolve b0e2849 b0e60761
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2849
      have b0e61230 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e7610 x
           have i₂ := b0e60761 x
           grind)
        | exact superpose b0e60761 b0e7610
        | (have j0 := b0e7610 x
           grind)
        | (have r₁ := b0e7610 x
           have r₂ := b0e60761 x
           grind)
        | exact resolve b0e7610 b0e60761
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7610 b0e60761
      have b0e61283 : x = (M.op x x) := by grind
      clear b0e61230
      have b0e61285 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have j0 := b0e61226 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61226
      have b0e61834 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e83 X0 x
           have i₂ := b0e61283
           grind)
        | exact superpose b0e61283 b0e83
        | exact resolve b0e83 b0e61283
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83 b0e61283
      have b0e66088 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e988 X0
           have i₂ := b0e61834 y
           grind)
        | exact superpose b0e61834 b0e988
        | (have j0 := b0e988 X0
           grind)
        | exact resolve b0e988 b0e61834
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e988
      have b0e66315 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e66088 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e66088
        | (have j0 := b0e66088 X0
           grind)
        | exact resolve b0e66088 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66088
      have b0e66316 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e66315 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66315
      have b0e66367 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e66316 X0
           have i₂ := b0e61285 X0
           grind)
        | exact superpose b0e61285 b0e66316
        | exact resolve b0e66316 b0e61285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61285 b0e66316
      have b0e66772 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e66367 (σ y)
           grind)
        | exact superpose b0e66367 b0e16
        | exact resolve b0e16 b0e66367
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66367
      have b0e67001 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e66772
           have i₂ := b0e61834 y
           grind)
        | exact superpose b0e61834 b0e66772
        | exact resolve b0e66772 b0e61834
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61834 b0e66772
      have b0e67041 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e67001
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e67001
        | exact resolve b0e67001 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67001
      have b0e67042 : False := by grind
      exact b0e67042
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
      have b1e54 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
      have b1e58 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e54 X0
           grind)
        | (have r₁ := b1e54 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e54 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e54 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e65 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e58 (σ y)
           grind)
        | exact superpose b1e58 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e58 (σ y)
           grind)
        | exact resolve b1e18 b1e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e58
      have b1e71 : False := by grind
      exact b1e71
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
      have b2e53 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
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
      have b2e57 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e53 X0
           grind)
        | (have r₁ := b2e53 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e53 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e53 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e53
      have b2e62 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e57 y
           grind)
        | exact superpose b2e57 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e57 y
           grind)
        | exact resolve b2e17 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e66 : False := by grind
      exact b2e66
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X1) := by
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
      have b3e21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X1)) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 (M.op X2 X1) X3
           have i₂ := b3e10 X2 X1 X0
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e23 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e10 x X1 X3
           have i₂ := b3e10 x X1 X0
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 X3 (M.op X1 X1)
           have i₂ := b3e10 X0 (M.op X1 X1) X1
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
      have b3e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op X2 (M.op (M.op X3 X3) X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 (M.op (M.op X3 X3) X1) X3
           have i₂ := b3e10 (M.op X3 X3) X1 X0
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b3e36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
      have b3e39 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
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
      have b3e40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
      have b3e41 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 X0 X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e42 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have j0 := b3e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e43 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e36 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e45 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e42 (σ X0)
           grind)
        | exact superpose b3e42 b3e15
        | exact resolve b3e15 b3e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e32 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e32
        | exact resolve b3e32 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e60 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b3e32 X0 y
           have i₂ := b3e42 X0
           grind)
        | exact superpose b3e42 b3e32
        | exact resolve b3e32 b3e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e32
      have b3e95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 (M.op X1 X1) X2 X3
           have i₂ := b3e23 X1 (M.op (M.op X1 X1) X2) X0
           grind)
        | (have i₁ := b3e10 (M.op X1 X1) X2 X3
           have i₂ := b3e23 X0 (M.op (M.op X1 X1) X2) X1
           grind)
        | exact superpose b3e23 b3e10
        | exact resolve b3e10 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e100 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e45 y
           grind)
        | exact superpose b3e45 b3e18
        | exact resolve b3e18 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e102 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ (k y y)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e23 (σ y) X0 X1
           have i₂ := b3e45 y
           grind)
        | exact superpose b3e45 b3e23
        | exact resolve b3e23 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e104 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ (k y y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X0 X1 (σ y)
           have i₂ := b3e45 y
           grind)
        | exact superpose b3e45 b3e10
        | exact resolve b3e10 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e125 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
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
      have b3e164 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e100
           have i₂ := b3e43 y y X0
           grind)
        | exact superpose b3e43 b3e100
        | (have j1 := b3e43 y x X0
           grind)
        | exact resolve b3e100 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e100
      have b3e167 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e43 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b3e43 b3e15
        | (have j1 := b3e43 (σ X0) X2 X2
           grind)
        | exact resolve b3e15 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e43
      have b3e171 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b3e164 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e164
      have b3e190 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X0 (M.op (M.op X4 X4) X2)) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b3e21 X4 X2 X0 x
           have i₂ := b3e21 X1 X2 X0 x
           grind)
        | (have i₁ := b3e21 X0 X1 (M.op X0 X0) x
           have i₂ := b3e21 X0 X1 (M.op x x) x
           grind)
        | exact superpose b3e21 b3e21
        | exact resolve b3e21 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e257 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e171 (τ X0)
           grind)
        | exact superpose b3e171 b3e19
        | exact resolve b3e19 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e259 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e257 X0
           have i₂ := b3e42 X0
           grind)
        | exact superpose b3e42 b3e257
        | exact resolve b3e257 b3e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42 b3e257
      have b3e387 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op X0 (M.op (M.op X1 X1) X2))) = (M.op (M.op X4 (M.op X4 (M.op X5 X5))) (M.op X0 X2)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e25 X4 X5 (M.op X3 X3) (M.op X0 X2)
           have i₂ := b3e21 X1 X2 X0 X3
           grind)
        | (have i₁ := b3e25 X0 X1 X2 (M.op (M.op X0 X0) X1)
           have i₂ := b3e21 X0 X1 X2 X3
           grind)
        | exact superpose b3e21 b3e25
        | exact resolve b3e25 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25
      have b3e504 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op X3 (M.op X3 (M.op (M.op X4 X4) X2))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e27 (M.op X1 X1) X2 X3 X4
           have i₂ := b3e23 X1 (M.op X1 X1) X0
           grind)
        | (have i₁ := b3e27 (M.op X1 X1) X2 X3 X4
           have i₂ := b3e23 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b3e23 b3e27
        | exact resolve b3e27 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e623 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op X2 (M.op (M.op X3 X3) (M.op (M.op X4 X4) X1)))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 X2 (M.op (M.op X3 X3) (M.op (M.op X4 X4) X1)) X3
           have i₂ := b3e27 X0 X1 (M.op X3 X3) X4
           grind)
        | exact superpose b3e27 b3e10
        | exact resolve b3e10 b3e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27
      have b3e780 : ∀ X0 X1 : G, (k (τ (M.op (σ y) X1)) y) = (τ (M.op (M.op X0 X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e60 (M.op (σ y) X1)
           have i₂ := b3e10 (σ y) X1 X0
           grind)
        | exact superpose b3e10 b3e60
        | exact resolve b3e60 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e796 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op y (τ (M.op (σ y) X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e780 X0 X1
           have i₂ := b3e171 (τ (M.op (σ y) X1))
           grind)
        | exact superpose b3e171 b3e780
        | exact resolve b3e780 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e780
      have b3e802 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op y (k (τ X1) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e796 X0 X1
           have i₂ := b3e60 X1
           grind)
        | exact superpose b3e60 b3e796
        | exact resolve b3e796 b3e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e60 b3e796
      have b3e808 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op y (M.op y (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e802 X0 X1
           have i₂ := b3e171 (τ X1)
           grind)
        | exact superpose b3e171 b3e802
        | exact resolve b3e802 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e802
      have b3e911 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e259 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e259
        | exact resolve b3e259 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e259
      have b3e1019 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e13 X1 (σ X0)
           have i₂ := b3e40 X0 X0
           grind)
        | exact superpose b3e40 b3e13
        | (have j0 := b3e13 X1 (σ X0)
           have j1 := b3e40 X0 X1
           grind)
        | (have r₁ := b3e13 X0 (σ X0)
           have r₂ := b3e40 X0 X1
           grind)
        | exact resolve b3e13 b3e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1068 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e40 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40
      have b3e1073 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b3e1019 X0 X1
           have j1 := b3e13 X1 (σ X0)
           grind)
        | (have r₁ := b3e1019 X0 X1
           have r₂ := b3e13 X0 (σ X0)
           grind)
        | exact resolve b3e1019 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1019
      have b3e1102 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ (M.op y y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e23 X0 X1 (σ y)
           have i₂ := b3e911 y
           grind)
        | exact superpose b3e911 b3e23
        | exact resolve b3e23 b3e911
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1111 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ y) (σ (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e26 X1 (σ X0) (σ y)
           have i₂ := b3e911 X0
           grind)
        | exact superpose b3e911 b3e26
        | exact resolve b3e26 b3e911
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e911
      have b3e1116 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (k (M.op y X0) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e1111 X0 X1
           have i₂ := b3e45 (M.op y X0)
           grind)
        | exact superpose b3e45 b3e1111
        | exact resolve b3e1111 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e45 b3e1111
      have b3e1126 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op y (M.op y X0))) := by
        intro X0 X1
        first
        | (have i₁ := b3e1116 X0 X1
           have i₂ := b3e171 (M.op y X0)
           grind)
        | exact superpose b3e171 b3e1116
        | exact resolve b3e1116 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1116
      have b3e1676 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X2) = (M.op (σ (k y y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e102 X2 (M.op X1 X1)
           have i₂ := b3e10 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b3e10 b3e102
        | exact resolve b3e102 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1679 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op (σ (k y y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e102 X2 (M.op X1 X1)
           have i₂ := b3e23 X1 (M.op X1 X1) X0
           grind)
        | (have i₁ := b3e102 X2 (M.op X1 X1)
           have i₂ := b3e23 X0 (M.op X1 X1) X1
           grind)
        | exact superpose b3e23 b3e102
        | exact resolve b3e102 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e102
      have b3e1983 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) = (M.op (σ (M.op y y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1679 X0 X1 X2
           have i₂ := b3e171 y
           grind)
        | exact superpose b3e171 b3e1679
        | exact resolve b3e1679 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1679
      have b3e1986 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X2) = (M.op (σ (M.op y y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1676 X0 X1 X2
           have i₂ := b3e171 y
           grind)
        | exact superpose b3e171 b3e1676
        | exact resolve b3e1676 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1676
      have b3e2027 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1073 (τ X0) X1
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e1073
        | (have j0 := b3e1073 (τ X0) X1
           grind)
        | exact resolve b3e1073 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1073
      have b3e2035 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2027 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e2027
        | (have j0 := b3e2027 X0 X1
           grind)
        | exact resolve b3e2027 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2027
      have b3e2039 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2035 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e2035
        | (have j0 := b3e2035 X0 X1
           grind)
        | exact resolve b3e2035 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2035
      have b3e2059 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2039 (τ X0) X1
           have i₂ := b3e56 X0 X0
           grind)
        | exact superpose b3e56 b3e2039
        | (have j0 := b3e2039 (τ X0) X1
           grind)
        | exact resolve b3e2039 b3e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e56 b3e2039
      have b3e2209 : ∀ X0 X1 X2 : G, (M.op (σ (k y y)) X0) = (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e23 X1 (M.op (M.op X2 X2) X0) X2
           have i₂ := b3e104 (M.op X2 X2) X0
           grind)
        | exact superpose b3e104 b3e23
        | exact resolve b3e23 b3e104
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e104
      have b3e2335 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = (M.op (σ (M.op y y)) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e2209 X0 X1 X2
           have i₂ := b3e171 y
           grind)
        | exact superpose b3e171 b3e2209
        | exact resolve b3e2209 b3e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e171 b3e2209
      have b3e2619 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e41 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e41
        | (have j0 := b3e41 X1 X1
           grind)
        | exact resolve b3e41 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e41
      have b3e2762 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2619 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e2619
        | (have j0 := b3e2619 X0 X1
           grind)
        | exact resolve b3e2619 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2619
      have b3e6645 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X2 (M.op X3 (M.op (M.op X4 X4) X1)))) = (M.op X3 (M.op (M.op X5 X5) (M.op (M.op X0 X0) X1))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e125 (M.op X5 X5) (M.op (M.op X4 X4) X1) X2 X3
           have i₂ := b3e95 X5 X4 X1 X0
           grind)
        | exact superpose b3e95 b3e125
        | exact resolve b3e125 b3e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e125
      have b3e7020 : ∀ X1 X2 X3 X4 : G, (M.op X2 (M.op X2 (M.op X3 (M.op (M.op X4 X4) X1)))) = (M.op X3 (M.op (σ (M.op y y)) X1)) := by
        intro X1 X2 X3 X4
        first
        | (have i₁ := b3e6645 x X1 X2 X3 X4 x
           have i₂ := b3e2335 X1 x x
           grind)
        | exact superpose b3e2335 b3e6645
        | exact resolve b3e6645 b3e2335
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2335 b3e6645
      have b3e20826 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (σ (M.op y (M.op y (τ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b3e12 (M.op (M.op X1 X1) X0)
           have i₂ := b3e808 X1 X0
           grind)
        | exact superpose b3e808 b3e12
        | exact resolve b3e12 b3e808
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e808
      have b3e24826 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e1068 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e1068
        | (have j0 := b3e1068 (τ X0)
           grind)
        | exact resolve b3e1068 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e24855 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e24826 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e24826
        | (have j0 := b3e24826 X0
           grind)
        | exact resolve b3e24826 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24826
      have b3e24867 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e24855 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e24855
        | (have j0 := b3e24855 X0
           grind)
        | exact resolve b3e24855 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24855
      have b3e27454 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e167 x y X0
           grind)
        | exact superpose b3e167 b3e16
        | (have j1 := b3e167 x x X0
           grind)
        | exact resolve b3e16 b3e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e167
      have b3e38811 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e20826 X1 X2
           have i₂ := b3e26 y (τ X1) X0
           grind)
        | (have i₁ := b3e20826 X1 X2
           have i₂ := b3e26 X0 (τ X1) y
           grind)
        | exact superpose b3e26 b3e20826
        | exact resolve b3e20826 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26 b3e20826
      have b3e56345 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ X0)) = (σ (M.op X2 (M.op X2 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e38811 X2 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e38811
        | exact resolve b3e38811 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38811
      have b3e109978 : ∀ X0 X1 X3 : G, (σ (M.op X0 (M.op X0 X1))) = (σ (M.op X3 (M.op X3 X1))) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e56345 X1 x X3
           have i₂ := b3e56345 X1 x X0
           grind)
        | exact superpose b3e56345 b3e56345
        | exact resolve b3e56345 b3e56345
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e56345
      have b3e180091 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X1)) = (σ (M.op X2 (M.op X2 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e109978 X2 X1 (M.op x x)
           have i₂ := b3e95 x x X1 X0
           grind)
        | exact superpose b3e95 b3e109978
        | exact resolve b3e109978 b3e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e95 b3e109978
      have b3e652770 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e27454 X0
           have i₂ := b3e2762 y x
           grind)
        | exact superpose b3e2762 b3e27454
        | (have j0 := b3e27454 X0
           have j1 := b3e2762 X0 x
           grind)
        | (have r₁ := b3e27454 X0
           have r₂ := b3e2762 y x
           grind)
        | exact resolve b3e27454 b3e2762
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2762 b3e27454
      have b3e652772 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e652770 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e652770
      have b3e657524 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e2059 (σ x) X0
           have i₂ := b3e652772 (σ x)
           grind)
        | exact superpose b3e652772 b3e2059
        | (have j0 := b3e2059 (σ x) X0
           grind)
        | exact resolve b3e2059 b3e652772
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2059 b3e652772
      have b3e657553 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e657524 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e657524
      have b3e657570 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e657553 X0
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e657553
        | exact resolve b3e657553 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e657553
      have b3e657582 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e657570 X0
           have j1 := b3e13 X0 x
           grind)
        | (have r₁ := b3e657570 X0
           have r₂ := b3e13 X0 x
           grind)
        | exact resolve b3e657570 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e657570
      have b3e662069 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e1068 x
           have i₂ := b3e657582 x
           grind)
        | exact superpose b3e657582 b3e1068
        | (have j0 := b3e1068 x
           grind)
        | exact resolve b3e1068 b3e657582
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1068
      have b3e662073 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e24867 x
           have i₂ := b3e657582 x
           grind)
        | exact superpose b3e657582 b3e24867
        | (have j0 := b3e24867 x
           grind)
        | (have r₁ := b3e24867 x
           have r₂ := b3e657582 x
           grind)
        | exact resolve b3e24867 b3e657582
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24867 b3e657582
      have b3e662140 : x = (M.op x x) := by grind
      clear b3e662073
      have b3e662144 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e662069
      have b3e666699 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X0 X1 x
           have i₂ := b3e662140
           grind)
        | exact superpose b3e662140 b3e10
        | exact resolve b3e10 b3e662140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e666702 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X2) X1)) = (M.op x (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e21 X2 X1 X0 x
           have i₂ := b3e662140
           grind)
        | exact superpose b3e662140 b3e21
        | exact resolve b3e21 b3e662140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21
      have b3e666705 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e23 X0 X1 x
           have i₂ := b3e662140
           grind)
        | exact superpose b3e662140 b3e23
        | exact resolve b3e23 b3e662140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23
      have b3e666743 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X0 (M.op x X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e190 X0 X1 X2 x
           have i₂ := b3e662140
           grind)
        | exact superpose b3e662140 b3e190
        | exact resolve b3e190 b3e662140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e190
      have b3e666882 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op X2 (M.op x (M.op (M.op X3 X3) X1)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e623 X0 X1 X2 x X3
           have i₂ := b3e662140
           grind)
        | exact superpose b3e662140 b3e623
        | exact resolve b3e623 b3e662140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e623
      have b3e667018 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (σ (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e180091 x X0 X1
           have i₂ := b3e662140
           grind)
        | exact superpose b3e662140 b3e180091
        | exact resolve b3e180091 b3e662140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e180091 b3e662140
      have b3e667262 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x (M.op (σ (M.op y y)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e666882 X0 X1 x x
           have i₂ := b3e7020 X1 x x x
           grind)
        | exact superpose b3e7020 b3e666882
        | exact resolve b3e666882 b3e7020
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e7020 b3e666882
      have b3e667361 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op X0 (M.op x X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e666702 X0 X1 x
           have i₂ := b3e666705 x X1
           grind)
        | exact superpose b3e666705 b3e666702
        | exact resolve b3e666702 b3e666705
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e666702
      have b3e667440 : ∀ X1 : G, (M.op x X1) = (M.op x (M.op (σ (M.op y y)) X1)) := by
        intro X1
        first
        | (have i₁ := b3e667262 x X1
           have i₂ := b3e666705 x X1
           grind)
        | exact superpose b3e666705 b3e667262
        | exact resolve b3e667262 b3e666705
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e666705 b3e667262
      have b3e670491 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (M.op X2 X2) X3)) = (M.op (M.op (M.op X4 X4) (M.op X5 X5)) X3) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e504 X4 X5 X3 (M.op X2 X2) x
           have i₂ := b3e387 (M.op X2 X2) x X3 X2 X0 X1
           grind)
        | exact superpose b3e387 b3e504
        | exact resolve b3e504 b3e387
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e387 b3e504
      have b3e672315 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op (M.op X2 X2) X3)) = (M.op (σ (M.op y y)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e670491 X0 X1 X2 X3 x x
           have i₂ := b3e1983 x x X3
           grind)
        | exact superpose b3e1983 b3e670491
        | exact resolve b3e670491 b3e1983
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1983 b3e670491
      have b3e672545 : ∀ X0 X1 X3 : G, (M.op (σ (M.op y y)) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) (M.op x X3)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e672315 X0 X1 x X3
           have i₂ := b3e666743 (M.op X0 (M.op X0 (M.op X1 X1))) x X3
           grind)
        | exact superpose b3e666743 b3e672315
        | exact resolve b3e672315 b3e666743
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e666743 b3e672315
      have b3e672715 : ∀ X0 X1 X3 : G, (M.op (σ (M.op y y)) X3) = (M.op x (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b3e672545 X0 X1 X3
           have i₂ := b3e667361 (M.op X0 (M.op X0 (M.op X1 X1))) X3
           grind)
        | exact superpose b3e667361 b3e672545
        | exact resolve b3e672545 b3e667361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e667361 b3e672545
      have b3e672840 : ∀ X3 : G, (M.op (σ (M.op y y)) X3) = (M.op x (M.op (σ (M.op y y)) X3)) := by
        intro X3
        first
        | (have i₁ := b3e672715 x x X3
           have i₂ := b3e1986 x x X3
           grind)
        | exact superpose b3e1986 b3e672715
        | exact resolve b3e672715 b3e1986
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1986 b3e672715
      have b3e672942 : ∀ X3 : G, (M.op (σ (M.op y y)) X3) = (M.op x X3) := by
        intro X3
        first
        | (have i₁ := b3e672840 X3
           have i₂ := b3e667440 X3
           grind)
        | (have i₁ := b3e672840 X3
           have i₂ := b3e667440 (M.op (σ (M.op y y)) X3)
           grind)
        | exact superpose b3e667440 b3e672840
        | exact resolve b3e672840 b3e667440
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e667440 b3e672840
      have b3e714453 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b3e1102 (σ x) X0
           have i₂ := b3e662144
           grind)
        | exact superpose b3e662144 b3e1102
        | exact resolve b3e1102 b3e662144
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1102 b3e662144
      have b3e714751 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e714453 X0
           have i₂ := b3e672942 X0
           grind)
        | exact superpose b3e672942 b3e714453
        | exact resolve b3e714453 b3e672942
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e672942 b3e714453
      have b3e749144 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e714751 (σ y)
           grind)
        | exact superpose b3e714751 b3e16
        | exact resolve b3e16 b3e714751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e714751
      have b3e763628 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e1126 X0 x
           have i₂ := b3e666699 x (σ X0)
           grind)
        | exact superpose b3e666699 b3e1126
        | exact resolve b3e1126 b3e666699
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1126 b3e666699
      have b3e764483 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e763628 X0
           have i₂ := b3e667018 X0 y
           grind)
        | exact superpose b3e667018 b3e763628
        | exact resolve b3e763628 b3e667018
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e667018 b3e763628
      have b3e888762 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e749144
           have i₂ := b3e764483 y
           grind)
        | exact superpose b3e764483 b3e749144
        | (have r₁ := b3e749144
           have r₂ := b3e764483 y
           grind)
        | exact resolve b3e749144 b3e764483
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e749144 b3e764483
      have b3e888763 : False := by grind
      exact b3e888763

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4428 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4428 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op y x) := by grind
        have b0e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e42 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 X0 X1 y x
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 X0 X1 x x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b0e42 x X1
             have i₂ := b0e43 x X1
             grind)
          | exact superpose b0e43 b0e42
          | exact resolve b0e42 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42 b0e43
        have b0e54 : y = (M.op x x) := by
          first
          | (have i₁ := b0e18
             have i₂ := b0e48 x
             grind)
          | exact superpose b0e48 b0e18
          | exact resolve b0e18 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48
        have b0e55 : x = y := by
          first
          | (have i₁ := b0e54
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e54
          | exact resolve b0e54 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e54
        have b0e66 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e55
             grind)
          | exact superpose b0e55 b0e17
          | exact resolve b0e17 b0e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e68 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e55
             grind)
          | exact superpose b0e55 b0e19
          | exact resolve b0e19 b0e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e55
        have b0e70 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e66
             have i₂ := b0e68
             grind)
          | exact superpose b0e68 b0e66
          | exact resolve b0e66 b0e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e66 b0e68
        have b0e71 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e70
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e70
          | exact resolve b0e70 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e70
        have b0e72 : False := by grind
        exact b0e72
      · have b1e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op y x) := by grind
        have b1e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
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
        have b1e28 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e11 X3 (M.op X3 X2) X4 X5
             have i₂ := b1e11 X3 X2 X0 X1
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e11 (M.op X2 X3) X1 X4 X5
             have i₂ := b1e11 X0 X1 X2 X3
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 (σ y) (σ x) X0 X1
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 X1 (σ y) (σ x)
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 X0 X1 y x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X3 ∨ (M.op X3 X2) = (k (M.op X3 X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e14 (M.op X3 X2) X3
             have i₂ := b1e11 X3 X2 X0 X1
             grind)
          | exact superpose b1e11 b1e14
          | (have j0 := b1e14 (M.op X3 X2) X3
             grind)
          | (have r₁ := b1e14 (M.op (M.op (M.op X2 X3) X1) X1) (M.op (M.op X2 X3) X1)
             have r₂ := b1e11 (M.op (M.op X2 X3) X1) X1 X2 X3
             grind)
          | (have r₁ := b1e14 X1 (M.op X0 (M.op X0 X1))
             have r₂ := b1e11 X0 X1 X0 (M.op X0 X1)
             grind)
          | exact resolve b1e14 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X3) ∨ (k X1 (M.op X2 X3)) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e14 X1 (M.op X2 X3)
             have i₂ := b1e11 X0 X1 X2 X3
             grind)
          | exact superpose b1e11 b1e14
          | (have j0 := b1e14 X1 (M.op X2 X3)
             grind)
          | (have r₁ := b1e14 (M.op (M.op (M.op X2 X3) X1) X1) (M.op (M.op X2 X3) X1)
             have r₂ := b1e11 (M.op (M.op X2 X3) X1) X1 X2 X3
             grind)
          | (have r₁ := b1e14 X1 (M.op X0 (M.op X0 X1))
             have r₂ := b1e11 X0 X1 X0 (M.op X0 X1)
             grind)
          | exact resolve b1e14 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
          intro X1
          first
          | (have i₁ := b1e35 x X1
             have i₂ := b1e36 x X1
             grind)
          | exact superpose b1e36 b1e35
          | exact resolve b1e35 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e42 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op y X1)) := by
          intro X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e29 x X1 X2 X3 X4 X5
             have i₂ := b1e36 x X1
             grind)
          | exact superpose b1e36 b1e29
          | exact resolve b1e29 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e49 : (σ y) = (M.op y (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e41 (σ x)
             grind)
          | exact superpose b1e41 b1e19
          | exact resolve b1e19 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e60 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 X1 (M.op X1 X0)
             have i₂ := b1e36 X1 X0
             grind)
          | exact superpose b1e36 b1e36
          | exact resolve b1e36 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : y = (M.op y y) := by
          first
          | (have i₁ := b1e36 y x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e36
          | exact resolve b1e36 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b1e36 y (σ x)
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e36
          | exact resolve b1e36 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e70 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e11 x X0 X2 X3
             have i₂ := b1e36 x X0
             grind)
          | exact superpose b1e36 b1e11
          | exact resolve b1e11 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X2 X3) (M.op X1 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e11 X1 (M.op X1 X0) X2 X3
             have i₂ := b1e36 X1 X0
             grind)
          | exact superpose b1e36 b1e11
          | exact resolve b1e11 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e95 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k (τ X0) X1)
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e403 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e95 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e95
          | exact resolve b1e95 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e779 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) (M.op X6 (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op (M.op X1 X2) X3))) := by
          intro X0 X1 X2 X3 X4 X5 X6
          first
          | (have i₁ := b1e28 x x (M.op X0 X3) X6 X4 X5
             have i₂ := b1e28 X1 X2 X3 X0 x x
             grind)
          | (have i₁ := b1e28 X0 X1 (M.op (M.op X0 X1) X2) X3 X4 X5
             have i₂ := b1e28 X0 X1 X2 (M.op X0 X1) X4 X5
             grind)
          | exact superpose b1e28 b1e28
          | exact resolve b1e28 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e814 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X6 X7) (M.op y (M.op X0 X3))) := by
          intro X0 X1 X2 X3 X6 X7
          first
          | (have i₁ := b1e42 (M.op X0 X3) X6 X7 x x
             have i₂ := b1e28 X1 X2 X3 X0 x x
             grind)
          | (have i₁ := b1e42 (M.op (M.op X0 X1) X2) X2 X3 x x
             have i₂ := b1e28 X0 X1 X2 (M.op x x) x x
             grind)
          | exact superpose b1e28 b1e42
          | exact resolve b1e42 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e42
        have b1e860 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op (M.op X6 X7) (M.op X0 X3))) := by
          intro X0 X1 X2 X3 X6 X7
          first
          | (have i₁ := b1e814 X0 X1 X2 X3 X6 X7
             have i₂ := b1e60 (M.op X0 X3) (M.op X6 X7)
             grind)
          | exact superpose b1e60 b1e814
          | exact resolve b1e814 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e814
        have b1e887 : ∀ X0 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) (M.op X6 (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op y X3))) := by
          intro X0 X3 X4 X5 X6
          first
          | (have i₁ := b1e779 X0 x x X3 X4 X5 X6
             have i₂ := b1e70 X3 x x
             grind)
          | exact superpose b1e70 b1e779
          | exact resolve b1e779 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e779
        have b1e945 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op y (M.op X0 (M.op y X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e860 X0 X1 X2 X3 x x
             have i₂ := b1e73 X3 X0 x x
             grind)
          | exact superpose b1e73 b1e860
          | exact resolve b1e860 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e860
        have b1e968 : ∀ X0 X3 X6 : G, (M.op X6 (M.op X0 (M.op y X3))) = (M.op X6 (M.op y (M.op X0 X3))) := by
          intro X0 X3 X6
          first
          | (have i₁ := b1e887 X0 X3 x x X6
             have i₂ := b1e73 (M.op X0 X3) X6 x x
             grind)
          | exact superpose b1e73 b1e887
          | exact resolve b1e887 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73 b1e887
        have b1e1007 : ∀ X0 X3 : G, (M.op X0 (M.op y X3)) = (M.op y (M.op X0 (M.op y X3))) := by
          intro X0 X3
          first
          | (have i₁ := b1e945 X0 x x X3
             have i₂ := b1e70 X3 x x
             grind)
          | exact superpose b1e70 b1e945
          | exact resolve b1e945 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e945
        have b1e1128 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op y (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b1e60 (σ x) X0
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e60
          | exact resolve b1e60 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1831 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (k (M.op (M.op (M.op X0 X1) X2) X2) (M.op (M.op X0 X1) X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e39 X0 X1 X2 (M.op (M.op X0 X1) X2)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e1832 : ∀ X2 : G, (M.op (M.op y X2) X2) = (k (M.op (M.op y X2) X2) (M.op y X2)) := by
          intro X2
          first
          | (have i₁ := b1e1831 X2 x x
             have i₂ := b1e70 x X2 x
             grind)
          | exact superpose b1e70 b1e1831
          | exact resolve b1e1831 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1831
        have b1e1849 : ∀ X2 : G, (M.op y X2) = (k (M.op y X2) (M.op y X2)) := by
          intro X2
          first
          | (have i₁ := b1e1832 x
             have i₂ := b1e70 x y x
             grind)
          | exact superpose b1e70 b1e1832
          | exact resolve b1e1832 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1832
        have b1e1968 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e40 X0 X0 X1 (M.op X1 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e1969 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e1968 X0 x
             have i₂ := b1e36 x X0
             grind)
          | exact superpose b1e36 b1e1968
          | exact resolve b1e1968 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1968
        have b1e2062 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op y (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b1e26 X0 (M.op y (τ X0))
             have i₂ := b1e1969 (τ X0)
             grind)
          | exact superpose b1e1969 b1e26
          | exact resolve b1e26 b1e1969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2063 : ∀ X0 : G, (k X0 (σ (M.op y (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2062 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2062
          | exact resolve b1e2062 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2062
        have b1e2092 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e56 X1 X0
             have i₂ := b1e56 X0 X1
             grind)
          | exact superpose b1e56 b1e56
          | (have j0 := b1e56 X1 X0
             have j1 := b1e56 X1 X0
             grind)
          | exact resolve b1e56 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2094 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ y)) ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b1e41 (σ X0)
             have i₂ := b1e56 y X0
             grind)
          | exact superpose b1e56 b1e41
          | (have j1 := b1e56 y X0
             grind)
          | exact resolve b1e41 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2104 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op y (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 (σ X0) (σ X1)
             have i₂ := b1e56 X0 X1
             grind)
          | exact superpose b1e56 b1e36
          | (have j1 := b1e56 X0 X1
             grind)
          | exact resolve b1e36 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2114 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e70 X2 (σ X0) (σ X1)
             have i₂ := b1e56 X0 X1
             grind)
          | exact superpose b1e56 b1e70
          | (have j1 := b1e56 X0 X1
             grind)
          | exact resolve b1e70 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2118 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (σ X1) (σ X0)
             have i₂ := b1e56 X1 X0
             grind)
          | exact superpose b1e56 b1e14
          | (have j0 := b1e14 (σ X1) (σ X0)
             have j1 := b1e56 X1 X0
             grind)
          | (have r₁ := b1e14 (σ X0) (σ X1)
             have r₂ := b1e56 X0 X1
             grind)
          | exact resolve b1e14 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2122 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ X0) (σ x)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 (σ X0) (σ X1)
             have i₂ := b1e56 X1 X0
             grind)
          | exact superpose b1e56 b1e30
          | (have j1 := b1e56 X1 X0
             grind)
          | exact resolve b1e30 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e2125 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 (σ X0) (σ X1)
             have i₂ := b1e56 X1 X0
             grind)
          | exact superpose b1e56 b1e36
          | (have j1 := b1e56 X1 X0
             grind)
          | exact resolve b1e36 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e2136 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e56 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2137 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e2118 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2118
        have b1e2147 : ∀ X0 X1 : G, (M.op y (σ y)) = (M.op (σ X0) (σ x)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e2122 X0 X1
             have i₂ := b1e41 (σ y)
             grind)
          | exact superpose b1e41 b1e2122
          | (have j0 := b1e2122 X0 X1
             grind)
          | exact resolve b1e2122 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2122
        have b1e2151 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e2137 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e2137
          | (have j0 := b1e2137 X0 X1
             grind)
          | exact resolve b1e2137 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2137
        have b1e2178 : ∀ X0 X1 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e2147 X0 X1
             have i₂ := b1e66
             grind)
          | exact superpose b1e66 b1e2147
          | (have j0 := b1e2147 X0 X1
             grind)
          | exact resolve b1e2147 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2147
        have b1e3611 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (k (M.op y (M.op X0 X1)) (M.op y (M.op X0 (M.op y X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1969 (M.op y (M.op X0 X1))
             have i₂ := b1e968 X0 X1 y
             grind)
          | (have i₁ := b1e1969 (M.op X0 (M.op y x))
             have i₂ := b1e968 X0 x y
             grind)
          | exact superpose b1e968 b1e1969
          | exact resolve b1e1969 b1e968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e968 b1e1969
        have b1e3665 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (k (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e3611 X0 X1
             have i₂ := b1e1007 X0 X1
             grind)
          | (have i₁ := b1e3611 y X1
             have i₂ := b1e1007 y (M.op y X1)
             grind)
          | exact superpose b1e1007 b1e3611
          | exact resolve b1e3611 b1e1007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3611
        have b1e4067 : ∀ X0 : G, (σ (M.op y X0)) ≠ (σ (M.op y X0)) ∨ (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e2136 (M.op y X0)
             have i₂ := b1e1849 X0
             grind)
          | exact superpose b1e1849 b1e2136
          | (have j0 := b1e2136 (M.op y X0)
             grind)
          | exact resolve b1e2136 b1e1849
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1849
        have b1e4076 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
          intro X0
          first
          | (have j0 := b1e4067 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4067
        have b1e4495 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) ∨ (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e2094 X0
             have i₂ := b1e2151 y X0
             grind)
          | exact superpose b1e2151 b1e2094
          | (have j0 := b1e2094 X0
             have j1 := b1e2151 y X0
             grind)
          | exact resolve b1e2094 b1e2151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2094
        have b1e4496 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e56 X1 X0
             have i₂ := b1e2151 X1 X0
             grind)
          | exact superpose b1e2151 b1e56
          | (have j0 := b1e56 X1 X0
             have j1 := b1e2151 X0 X1
             grind)
          | exact resolve b1e56 b1e2151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2151
        have b1e4526 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e4496 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4496
        have b1e4527 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have j0 := b1e4495 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4495
        have b1e4970 : ∀ X0 X1 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b1e56 x X0
             have i₂ := b1e2178 X0 X1
             grind)
          | exact superpose b1e2178 b1e56
          | (have j0 := b1e56 x X0
             have j1 := b1e2178 X0 x
             grind)
          | exact resolve b1e56 b1e2178
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e2178
        have b1e6064 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op X0 (σ (k (τ X0) X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e2104 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2104
          | exact resolve b1e2104 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6159 : ∀ X0 X1 : G, (M.op y (σ X1)) = (M.op X0 (k X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e6064 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e6064
          | (have j0 := b1e6064 X0 X1
             grind)
          | exact resolve b1e6064 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6064
        have b1e6277 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op y (σ X1)) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e2125 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2125
          | exact resolve b1e2125 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2125
        have b1e6462 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op y (σ X1)) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e6277 X0 X1
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e6277
          | (have j0 := b1e6277 X0 X1
             grind)
          | exact resolve b1e6277 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6277
        have b1e6805 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op y X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e70 X1 (σ (M.op y X0)) (σ (M.op y X0))
             have i₂ := b1e4076 X0
             grind)
          | exact superpose b1e4076 b1e70
          | exact resolve b1e70 b1e4076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e7040 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (M.op X0 (M.op y X1))) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e6805 (M.op X0 (M.op y X1)) X2
             have i₂ := b1e1007 X0 X1
             grind)
          | exact superpose b1e1007 b1e6805
          | exact resolve b1e6805 b1e1007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e7143 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e4076 X0
             have i₂ := b1e6805 X0 (σ (M.op y X0))
             grind)
          | exact superpose b1e6805 b1e4076
          | exact resolve b1e4076 b1e6805
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e10056 : ∀ X0 X1 : G, (σ (M.op X0 (M.op y X1))) = (M.op y (σ (M.op X0 (M.op y X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e7143 (M.op X0 (M.op y x))
             have i₂ := b1e1007 X0 x
             grind)
          | exact superpose b1e1007 b1e7143
          | exact resolve b1e7143 b1e1007
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1007
        have b1e11723 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e2092 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2092
          | exact resolve b1e2092 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2092
        have b1e11848 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e11723 X0 X1
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e11723
          | (have j0 := b1e11723 X0 X1
             grind)
          | exact resolve b1e11723 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11723
        have b1e11865 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e11848 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e11848
          | (have j0 := b1e11848 X0 X1
             grind)
          | exact resolve b1e11848 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e11848
        have b1e11875 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b1e11865 X0 X1
             have j1 := b1e14 X0 (σ X1)
             grind)
          | (have r₁ := b1e11865 X0 X1
             have r₂ := b1e14 X0 (σ X1)
             grind)
          | exact resolve b1e11865 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11865
        have b1e17002 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e11875 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e11875
          | exact resolve b1e11875 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11875
        have b1e21469 : ∀ X0 X1 : G, (M.op y (σ (M.op X0 (M.op y X1)))) = (M.op (σ (M.op y (M.op X0 X1))) (σ (M.op y (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op y X1))) = (M.op (σ (M.op X0 (M.op y X1))) (σ (M.op y (M.op X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2104 (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))
             have i₂ := b1e3665 X0 X1
             grind)
          | exact superpose b1e3665 b1e2104
          | (have j0 := b1e2104 (M.op y (M.op X0 X1)) (M.op X0 (M.op y X1))
             grind)
          | exact resolve b1e2104 b1e3665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2104 b1e3665
        have b1e21488 : ∀ X0 X1 : G, (M.op y (σ (M.op X0 (M.op y X1)))) = (σ (M.op y (M.op X0 X1))) ∨ (σ (M.op X0 (M.op y X1))) = (M.op (σ (M.op X0 (M.op y X1))) (σ (M.op y (M.op X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e21469 X0 X1
             have i₂ := b1e4076 (M.op X0 X1)
             grind)
          | exact superpose b1e4076 b1e21469
          | (have j0 := b1e21469 X0 X1
             grind)
          | exact resolve b1e21469 b1e4076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4076 b1e21469
        have b1e21629 : ∀ X0 X1 : G, (σ (M.op X0 (M.op y X1))) = (σ (M.op y (M.op X0 X1))) ∨ (σ (M.op X0 (M.op y X1))) = (M.op (σ (M.op X0 (M.op y X1))) (σ (M.op y (M.op X0 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e21488 X0 X1
             have i₂ := b1e10056 X0 X1
             grind)
          | exact superpose b1e10056 b1e21488
          | (have j0 := b1e21488 X0 X1
             grind)
          | exact resolve b1e21488 b1e10056
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10056 b1e21488
        have b1e21704 : ∀ X0 X1 : G, (σ (M.op X0 (M.op y X1))) = (M.op y (σ (M.op y (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op y X1))) = (σ (M.op y (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e21629 X0 X1
             have i₂ := b1e7040 X0 X1 (σ (M.op y (M.op X0 X1)))
             grind)
          | exact superpose b1e7040 b1e21629
          | (have j0 := b1e21629 X0 X1
             grind)
          | exact resolve b1e21629 b1e7040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7040 b1e21629
        have b1e21750 : ∀ X0 X1 : G, (σ (M.op X0 (M.op y X1))) = (σ (M.op y (M.op X0 X1))) ∨ (σ (M.op X0 (M.op y X1))) = (σ (M.op y (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e21704 X0 X1
             have i₂ := b1e7143 (M.op X0 X1)
             grind)
          | exact superpose b1e7143 b1e21704
          | (have j0 := b1e21704 X0 X1
             grind)
          | exact resolve b1e21704 b1e7143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21704
        have b1e21751 : ∀ X0 X1 : G, (σ (M.op X0 (M.op y X1))) = (σ (M.op y (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b1e21750 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21750
        have b1e25582 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (σ X1) (σ X0)
             have i₂ := b1e4526 X1 X0
             grind)
          | exact superpose b1e4526 b1e14
          | (have j0 := b1e14 (σ X1) (σ X0)
             have j1 := b1e4526 X1 X0
             grind)
          | exact resolve b1e14 b1e4526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4526
        have b1e25659 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e25582 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e25582
          | (have j0 := b1e25582 X0 X1
             grind)
          | exact resolve b1e25582 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25582
        have b1e25660 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e25659 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25659
        have b1e27451 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e6462 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e6462
          | exact resolve b1e6462 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6462
        have b1e28200 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e2114 (τ X0) (τ X1) X2
             have i₂ := b1e403 X1 X0
             grind)
          | exact superpose b1e403 b1e2114
          | (have j0 := b1e2114 (τ X0) (τ X1) X2
             grind)
          | exact resolve b1e2114 b1e403
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e403 b1e2114
        have b1e28482 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e28200 X0 X1 X2
             have i₂ := b1e13 (k X0 X1)
             grind)
          | exact superpose b1e13 b1e28200
          | (have j0 := b1e28200 X0 X1 X2
             grind)
          | exact resolve b1e28200 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28200
        have b1e28517 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op y X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e28482 X0 X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e28482
          | (have j0 := b1e28482 X0 X1 X2
             grind)
          | exact resolve b1e28482 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28482
        have b1e28531 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (k X0 X1) X2) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e28517 X0 X0 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e28517
          | (have j0 := b1e28517 X0 X1 X2
             grind)
          | exact resolve b1e28517 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28517
        have b1e32258 : ∀ X0 : G, (M.op X0 X0) = (M.op y (σ (M.op y (τ X0)))) ∨ (σ (M.op y (τ X0))) = (M.op (σ (M.op y (τ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b1e6159 X0 (M.op y (τ X0))
             have i₂ := b1e2063 X0
             grind)
          | exact superpose b1e2063 b1e6159
          | (have j0 := b1e6159 X0 (M.op y (τ X0))
             grind)
          | exact resolve b1e6159 b1e2063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6159
        have b1e32475 : ∀ X0 : G, (σ (M.op y (τ X0))) = (M.op X0 X0) ∨ (σ (M.op y (τ X0))) = (M.op (σ (M.op y (τ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b1e32258 X0
             have i₂ := b1e7143 (τ X0)
             grind)
          | exact superpose b1e7143 b1e32258
          | (have j0 := b1e32258 X0
             grind)
          | exact resolve b1e32258 b1e7143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7143 b1e32258
        have b1e32488 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) ∨ (σ (M.op y (τ X0))) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e32475 X0
             have i₂ := b1e6805 (τ X0) X0
             grind)
          | exact superpose b1e6805 b1e32475
          | (have j0 := b1e32475 X0
             grind)
          | exact resolve b1e32475 b1e6805
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32475
        have b1e102409 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e25660 X0 X1
             have i₂ := b1e17002 X1 X0
             grind)
          | exact superpose b1e17002 b1e25660
          | (have j0 := b1e25660 X0 X1
             have j1 := b1e17002 X1 X0
             grind)
          | exact resolve b1e25660 b1e17002
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17002
        have b1e102499 : ∀ X0 : G, (σ y) ≠ (M.op y (σ X0)) ∨ (σ X0) = (σ (k X0 y)) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e25660 y X0
             have i₂ := b1e4527 X0
             grind)
          | exact superpose b1e4527 b1e25660
          | (have j0 := b1e25660 y X0
             have j1 := b1e4527 X0
             grind)
          | (have r₁ := b1e25660 X0 y
             have r₂ := b1e4527 X0
             grind)
          | exact resolve b1e25660 b1e4527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4527 b1e25660
        have b1e102502 : ∀ X0 : G, (σ y) ≠ (M.op y (σ X0)) ∨ (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have j0 := b1e102499 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102499
        have b1e102530 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e102409 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102409
        have b1e105883 : ∀ X0 : G, y = (M.op X0 X0) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e18
             have i₂ := b1e27451 x X0
             grind)
          | exact superpose b1e27451 b1e18
          | (have j1 := b1e27451 x X0
             grind)
          | exact resolve b1e18 b1e27451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27451
        have b1e106703 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op X0 (M.op y X0))) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e21751 X0 X0
             have i₂ := b1e105883 X0
             grind)
          | exact superpose b1e105883 b1e21751
          | (have j1 := b1e105883 X0
             grind)
          | exact resolve b1e21751 b1e105883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21751 b1e105883
        have b1e106895 : ∀ X0 : G, (σ y) = (σ (M.op X0 (M.op y X0))) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e106703 X0
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e106703
          | (have j0 := b1e106703 X0
             grind)
          | exact resolve b1e106703 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e106703
        have b1e109525 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y X1) ∨ (σ (M.op y (τ X0))) = (M.op (σ (M.op y (τ X0))) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e28531 X0 (σ (M.op y (τ X0))) X1
             have i₂ := b1e2063 X0
             grind)
          | exact superpose b1e2063 b1e28531
          | (have j0 := b1e28531 X0 (σ (M.op y (τ X0))) x
             grind)
          | exact resolve b1e28531 b1e2063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2063 b1e28531
        have b1e109813 : ∀ X0 X1 : G, (M.op y X0) = (σ (M.op y (τ X0))) ∨ (M.op X0 X1) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e109525 X0 X1
             have i₂ := b1e6805 (τ X0) X0
             grind)
          | exact superpose b1e6805 b1e109525
          | (have j0 := b1e109525 X0 X1
             grind)
          | exact resolve b1e109525 b1e6805
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6805 b1e109525
        have b1e125978 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e2136 X0
             have i₂ := b1e102530 X0 X0
             grind)
          | exact superpose b1e102530 b1e2136
          | (have j0 := b1e2136 X0
             have j1 := b1e102530 X0 X0
             grind)
          | (have r₁ := b1e2136 X0
             have r₂ := b1e102530 X0 X0
             grind)
          | exact resolve b1e2136 b1e102530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2136 b1e102530
        have b1e126019 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have j0 := b1e125978 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e125978
        have b1e154998 : ∀ X0 : G, (σ (k x X0)) ≠ (σ (k x X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have j0 := b1e4970 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4970
        have b1e154999 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have j0 := b1e154998 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e154998
        have b1e311258 : ∀ X0 : G, (M.op (σ x) X0) = (σ (k x (τ X0))) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e154999 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e154999
          | exact resolve b1e154999 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e154999
        have b1e311290 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e311258 X0
             have i₂ := b1e27 X0 x
             grind)
          | exact superpose b1e27 b1e311258
          | (have j0 := b1e311258 X0
             grind)
          | exact resolve b1e311258 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e311258
        have b1e312080 : ∀ X0 : G, (k (τ (σ x)) X0) = (τ (M.op (σ x) (σ X0))) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e95 (σ x) X0
             have i₂ := b1e311290 (σ X0)
             grind)
          | exact superpose b1e311290 b1e95
          | (have j1 := b1e311290 (σ X0)
             grind)
          | exact resolve b1e95 b1e311290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e95 b1e311290
        have b1e312087 : ∀ X0 : G, (k x X0) = (τ (M.op (σ x) (σ X0))) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e312080 X0
             have i₂ := b1e12 x
             grind)
          | exact superpose b1e12 b1e312080
          | (have j0 := b1e312080 X0
             grind)
          | exact resolve b1e312080 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e312080
        have b1e360832 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ X0) X1) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e70 X1 (σ X0) (σ X0)
             have i₂ := b1e126019 X0
             grind)
          | exact superpose b1e126019 b1e70
          | (have j1 := b1e126019 X0
             grind)
          | exact resolve b1e70 b1e126019
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e126019
        have b1e407115 : (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (M.op x x) = (k x x) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e360832 x (σ y)
             grind)
          | exact superpose b1e360832 b1e17
          | (have j1 := b1e360832 x x
             grind)
          | exact resolve b1e17 b1e360832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e360832
        have b1e407129 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (k x x) := by
          first
          | (have i₁ := b1e407115
             have i₂ := b1e66
             grind)
          | exact superpose b1e66 b1e407115
          | exact resolve b1e407115 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e407115
        have b1e876491 : (σ (M.op x y)) = (σ y) ∨ (M.op x x) = (k x x) := by
          first
          | (have i₁ := b1e106895 x
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e106895
          | (have j0 := b1e106895 x
             grind)
          | exact resolve b1e106895 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106895
        have b1e876521 : (M.op x x) = (k x x) := by
          first
          | (have r₁ := b1e876491
             have r₂ := b1e407129
             grind)
          | exact resolve b1e876491 b1e407129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e407129 b1e876491
        have b1e878980 : ∀ X0 : G, (M.op y X0) ≠ (M.op X0 X0) ∨ (M.op y X0) = (σ (M.op y (τ X0))) := by
          intro X0
          first
          | (have j0 := b1e32488 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32488
        have b1e878985 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) := by
          intro X0
          first
          | (have j0 := b1e878980 X0
             have j1 := b1e109813 X0 x
             grind)
          | (have r₁ := b1e878980 y
             have r₂ := b1e109813 y y
             grind)
          | (have r₁ := b1e878980 X0
             have r₂ := b1e109813 X0 X0
             grind)
          | exact resolve b1e878980 b1e109813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e109813 b1e878980
        have b1e879129 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 (M.op y (τ X0))
             have i₂ := b1e878985 X0
             grind)
          | exact superpose b1e878985 b1e12
          | exact resolve b1e12 b1e878985
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e878985
        have b1e879762 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (M.op y (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b1e879129 (M.op X0 (σ x))
             have i₂ := b1e1128 X0
             grind)
          | exact superpose b1e1128 b1e879129
          | exact resolve b1e879129 b1e1128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1128 b1e879129
        have b1e884993 : (τ (M.op (σ x) (σ y))) = (M.op y (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e879762 (σ x)
             have i₂ := b1e312087 x
             grind)
          | exact superpose b1e312087 b1e879762
          | (have j1 := b1e312087 x
             grind)
          | exact resolve b1e879762 b1e312087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e312087 b1e879762
        have b1e885098 : (τ (M.op (σ x) (σ y))) = (M.op y (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e884993
             have i₂ := b1e876521
             grind)
          | exact superpose b1e876521 b1e884993
          | exact resolve b1e884993 b1e876521
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e884993
        have b1e885139 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e885098
             have i₂ := b1e60 x x
             grind)
          | exact superpose b1e60 b1e885098
          | exact resolve b1e885098 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e885098
        have b1e885153 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e885139
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e885139
          | exact resolve b1e885139 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e885139
        have b1e899747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e13 (M.op (σ x) (σ y))
             have i₂ := b1e885153
             grind)
          | exact superpose b1e885153 b1e13
          | exact resolve b1e13 b1e885153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e885153
        have b1e899748 : (σ x) = (σ y) := by
          first
          | (have r₁ := b1e899747
             have r₂ := b1e17
             grind)
          | exact resolve b1e899747 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e899747
        have b1e899750 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e899748
             grind)
          | exact superpose b1e899748 b1e17
          | exact resolve b1e17 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e899752 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e41 X0
             have i₂ := b1e899748
             grind)
          | exact superpose b1e899748 b1e41
          | exact resolve b1e41 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e900023 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e12 y
             have i₂ := b1e899748
             grind)
          | exact superpose b1e899748 b1e12
          | exact resolve b1e12 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e900024 : ∀ X0 : G, (σ (k y X0)) = (k (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e16 y X0
             have i₂ := b1e899748
             grind)
          | exact superpose b1e899748 b1e16
          | exact resolve b1e16 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e900025 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 y
             have i₂ := b1e899748
             grind)
          | exact superpose b1e899748 b1e16
          | exact resolve b1e16 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e900081 : (σ x) ≠ (M.op y (σ x)) ∨ (σ x) = (σ (k y y)) := by
          first
          | (have i₁ := b1e102502 y
             have i₂ := b1e899748
             grind)
          | exact superpose b1e899748 b1e102502
          | exact resolve b1e102502 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102502
        have b1e900157 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y y)) := by
          first
          | (have i₁ := b1e900081
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e900081
          | exact resolve b1e900081 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900081
        have b1e900181 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e900025 X0
             have i₂ := b1e16 X0 x
             grind)
          | exact superpose b1e16 b1e900025
          | exact resolve b1e900025 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900025
        have b1e900182 : ∀ X0 : G, (σ (k y X0)) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b1e900024 X0
             have i₂ := b1e16 x X0
             grind)
          | exact superpose b1e16 b1e900024
          | exact resolve b1e900024 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900024
        have b1e900183 : x = y := by
          first
          | (have i₁ := b1e900023
             have i₂ := b1e12 x
             grind)
          | exact superpose b1e12 b1e900023
          | exact resolve b1e900023 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900023
        have b1e900205 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
          first
          | (have i₁ := b1e899750
             have i₂ := b1e899752 (σ x)
             grind)
          | exact superpose b1e899752 b1e899750
          | exact resolve b1e899750 b1e899752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e899750 b1e899752
        have b1e900217 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e900157
             have r₂ := b1e899748
             grind)
          | exact resolve b1e900157 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900157
        have b1e900235 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e900205
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e900205
          | exact resolve b1e900205 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e900205
        have b1e900242 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b1e900217
             have i₂ := b1e900181 y
             grind)
          | exact superpose b1e900181 b1e900217
          | exact resolve b1e900217 b1e900181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900181 b1e900217
        have b1e900257 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e900235
             have i₂ := b1e899748
             grind)
          | exact superpose b1e899748 b1e900235
          | exact resolve b1e900235 b1e899748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e899748 b1e900235
        have b1e900261 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e900242
             have i₂ := b1e900182 x
             grind)
          | exact superpose b1e900182 b1e900242
          | exact resolve b1e900242 b1e900182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900182 b1e900242
        have b1e900270 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e900257
             have i₂ := b1e900183
             grind)
          | exact superpose b1e900183 b1e900257
          | exact resolve b1e900257 b1e900183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e900183 b1e900257
        have b1e900273 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e900261
             have i₂ := b1e876521
             grind)
          | exact superpose b1e876521 b1e900261
          | exact resolve b1e900261 b1e876521
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e876521 b1e900261
        have b1e900280 : False := by grind
        exact b1e900280
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b2e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b2e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e18 : y = (M.op y x) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e21 : y ≠ y ∨ x = (k x y) := by
          first
          | (have i₁ := b2e14 x y
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e14
          | (have j0 := b2e14 x y
             grind)
          | (have r₁ := b2e14 x y
             have r₂ := b2e18
             grind)
          | exact resolve b2e14 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e24 : x = (k x y) := by grind
        clear b2e21
        have b2e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 X0 X1 y x
             have i₂ := b2e18
             grind)
          | exact superpose b2e18 b2e11
          | exact resolve b2e11 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e11 X0 X1 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11
          | exact resolve b2e11 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b2e35 x X1
             have i₂ := b2e36 x X1
             grind)
          | exact superpose b2e36 b2e35
          | exact resolve b2e35 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e36
        have b2e48 : y = (M.op x x) := by
          first
          | (have i₁ := b2e18
             have i₂ := b2e43 x
             grind)
          | exact superpose b2e43 b2e18
          | exact resolve b2e18 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e49 : x = y := by
          first
          | (have i₁ := b2e48
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e48
          | exact resolve b2e48 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e62 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e19
          | exact resolve b2e19 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1847 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e54 x y
             grind)
          | exact superpose b2e54 b2e19
          | (have j1 := b2e54 x y
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e54 x y
             grind)
          | exact resolve b2e19 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e1869 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
        clear b2e1847
        have b2e1885 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1869
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1869
          | exact resolve b2e1869 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1869
        have b2e1911 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e1885
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e1885
          | exact resolve b2e1885 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e1885
        have b2e1922 : False := by grind
        exact b2e1922
      · have b3e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b3e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op y x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b3e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e21 : y ≠ y ∨ x = (k x y) := by
          first
          | (have i₁ := b3e14 x y
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e14
          | (have j0 := b3e14 x y
             grind)
          | (have r₁ := b3e14 x y
             have r₂ := b3e18
             grind)
          | exact resolve b3e14 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e22 : x = (k x y) := by grind
        clear b3e21
        have b3e29 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e11 X0 X1 y x
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e11
          | exact resolve b3e11 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X3 ∨ (M.op X3 X2) = (k (M.op X3 X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e14 (M.op X3 X2) X3
             have i₂ := b3e11 X3 X2 X0 X1
             grind)
          | exact superpose b3e11 b3e14
          | (have j0 := b3e14 (M.op X3 X2) X3
             grind)
          | (have r₁ := b3e14 (M.op (M.op (M.op X2 X3) X1) X1) (M.op (M.op X2 X3) X1)
             have r₂ := b3e11 (M.op (M.op X2 X3) X1) X1 X2 X3
             grind)
          | (have r₁ := b3e14 X1 (M.op X0 (M.op X0 X1))
             have r₂ := b3e11 X0 X1 X0 (M.op X0 X1)
             grind)
          | exact resolve b3e14 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e11 x X0 X2 X3
             have i₂ := b3e29 x X0
             grind)
          | exact superpose b3e29 b3e11
          | exact resolve b3e11 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e1556 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (k (M.op (M.op (M.op X0 X1) X2) X2) (M.op (M.op X0 X1) X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e34 X0 X1 X2 (M.op (M.op X0 X1) X2)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e1557 : ∀ X2 : G, (M.op (M.op y X2) X2) = (k (M.op (M.op y X2) X2) (M.op y X2)) := by
          intro X2
          first
          | (have i₁ := b3e1556 X2 x x
             have i₂ := b3e43 x X2 x
             grind)
          | exact superpose b3e43 b3e1556
          | exact resolve b3e1556 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1556
        have b3e1570 : ∀ X2 : G, (M.op y X2) = (k (M.op y X2) (M.op y X2)) := by
          intro X2
          first
          | (have i₁ := b3e1557 x
             have i₂ := b3e43 x y x
             grind)
          | exact superpose b3e43 b3e1557
          | exact resolve b3e1557 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1557
        have b3e1805 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e57 x y
             grind)
          | exact superpose b3e57 b3e19
          | (have j1 := b3e57 x y
             grind)
          | (have r₁ := b3e19
             have r₂ := b3e57 x y
             grind)
          | exact resolve b3e19 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e1827 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
        clear b3e1805
        have b3e1843 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e1827
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1827
          | exact resolve b3e1827 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22 b3e1827
        have b3e1897 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e43 X0 (σ x) (σ y)
             have i₂ := b3e1843
             grind)
          | exact superpose b3e1843 b3e43
          | exact resolve b3e43 b3e1843
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e2586 : (σ x) = (M.op y (σ y)) := by
          first
          | (have i₁ := b3e1843
             have i₂ := b3e1897 (σ y)
             grind)
          | exact superpose b3e1897 b3e1843
          | exact resolve b3e1843 b3e1897
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1843 b3e1897
        have b3e2664 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1570 (σ y)
             have i₂ := b3e2586
             grind)
          | exact superpose b3e2586 b3e1570
          | exact resolve b3e1570 b3e2586
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1570 b3e2586
        have b3e2701 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e2664
             have i₂ := b3e16 x x
             grind)
          | exact superpose b3e16 b3e2664
          | exact resolve b3e2664 b3e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2664
        have b3e2791 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e12 (k x x)
             have i₂ := b3e2701
             grind)
          | exact superpose b3e2701 b3e12
          | exact resolve b3e12 b3e2701
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2701
        have b3e2816 : x = (k x x) := by
          first
          | (have i₁ := b3e2791
             have i₂ := b3e12 x
             grind)
          | exact superpose b3e12 b3e2791
          | exact resolve b3e2791 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2791
        have b3e2852 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e15 x x
             have i₂ := b3e2816
             grind)
          | exact superpose b3e2816 b3e15
          | (have j0 := b3e15 x x
             grind)
          | exact resolve b3e15 b3e2816
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2816
        have b3e2853 : x = (M.op x x) := by grind
        clear b3e2852
        have b3e2855 : False := by grind
        exact b3e2855
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op y x) := by grind
        have b4e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b4e20 : x = (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e22 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b4e14 (σ x) (σ y)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e14
          | (have j0 := b4e14 (σ x) (σ y)
             grind)
          | (have r₁ := b4e14 (σ x) (σ y)
             have r₂ := b4e19
             grind)
          | exact resolve b4e14 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e23 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b4e22
        have b4e25 : (σ x) = (σ (k x y)) := by
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
        have b4e41 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b4e11 X0 X1 (σ y) (σ x)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e11
          | exact resolve b4e11 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e42 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b4e11 X0 X1 x x
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e11 X0 X1 x x
             have i₂ := b4e11 X2 X1 x x
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e46 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X3) ∨ (k X1 (M.op X2 X3)) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b4e14 X1 (M.op X2 X3)
             have i₂ := b4e11 X0 X1 X2 X3
             grind)
          | exact superpose b4e11 b4e14
          | (have j0 := b4e14 X1 (M.op X2 X3)
             grind)
          | (have r₁ := b4e14 (M.op (M.op (M.op X2 X3) X1) X1) (M.op (M.op X2 X3) X1)
             have r₂ := b4e11 (M.op (M.op X2 X3) X1) X1 X2 X3
             grind)
          | (have r₁ := b4e14 X1 (M.op X0 (M.op X0 X1))
             have r₂ := b4e11 X0 X1 X0 (M.op X0 X1)
             grind)
          | exact resolve b4e14 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e47 : ∀ X1 : G, (M.op (σ y) X1) = (M.op x X1) := by
          intro X1
          first
          | (have i₁ := b4e41 x X1
             have i₂ := b4e42 x X1
             grind)
          | exact superpose b4e42 b4e41
          | exact resolve b4e41 b4e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e41
        have b4e55 : (σ y) = (M.op x (σ x)) := by
          first
          | (have i₁ := b4e19
             have i₂ := b4e47 (σ x)
             grind)
          | exact superpose b4e47 b4e19
          | exact resolve b4e19 b4e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e63 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b4e31
             have i₂ := b4e15 x y
             grind)
          | exact superpose b4e15 b4e31
          | (have j1 := b4e15 y x
             grind)
          | exact resolve b4e31 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e31
        have b4e69 : x = (M.op x y) := by
          first
          | (have r₁ := b4e63
             have r₂ := b4e18
             grind)
          | exact resolve b4e63 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e63
        have b4e77 : (M.op (σ y) (σ y)) = (M.op x (σ x)) := by
          first
          | (have i₁ := b4e42 (σ y) (σ x)
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e42
          | exact resolve b4e42 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e95 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b4e77
             have i₂ := b4e55
             grind)
          | exact superpose b4e55 b4e77
          | exact resolve b4e77 b4e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e55 b4e77
        have b4e100 : (σ y) = (M.op x (σ y)) := by
          first
          | (have i₁ := b4e95
             have i₂ := b4e47 (σ y)
             grind)
          | exact superpose b4e47 b4e95
          | exact resolve b4e95 b4e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e47 b4e95
        have b4e1918 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
          intro X0 X1
          first
          | (have j0 := b4e46 X0 X0 X1 (M.op X1 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e46
        have b4e1919 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b4e1918 X0 x
             have i₂ := b4e42 x X0
             grind)
          | exact superpose b4e42 b4e1918
          | exact resolve b4e1918 b4e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1918
        have b4e1998 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b4e1919 (σ y)
             have i₂ := b4e100
             grind)
          | exact superpose b4e100 b4e1919
          | exact resolve b4e1919 b4e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e100 b4e1919
        have b4e2016 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b4e1998
             have i₂ := b4e16 y y
             grind)
          | exact superpose b4e16 b4e1998
          | exact resolve b4e1998 b4e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1998
        have b4e2156 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b4e12 (k y y)
             have i₂ := b4e2016
             grind)
          | exact superpose b4e2016 b4e12
          | exact resolve b4e12 b4e2016
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2016
        have b4e2173 : y = (k y y) := by
          first
          | (have i₁ := b4e2156
             have i₂ := b4e12 y
             grind)
          | exact superpose b4e12 b4e2156
          | exact resolve b4e2156 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2156
        have b4e2450 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b4e15 y y
             have i₂ := b4e2173
             grind)
          | exact superpose b4e2173 b4e15
          | (have j0 := b4e15 y y
             grind)
          | exact resolve b4e15 b4e2173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2173
        have b4e2451 : y = (M.op y y) := by grind
        clear b4e2450
        have b4e2489 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b4e43 X0 y y
             have i₂ := b4e2451
             grind)
          | exact superpose b4e2451 b4e43
          | exact resolve b4e43 b4e2451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e43
        have b4e2502 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b4e2489 X0
             have i₂ := b4e2451
             grind)
          | exact superpose b4e2451 b4e2489
          | exact resolve b4e2489 b4e2451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2451 b4e2489
        have b4e2514 : y = (M.op x y) := by
          first
          | (have i₁ := b4e2502 x
             have i₂ := b4e42 x y
             grind)
          | exact superpose b4e42 b4e2502
          | exact resolve b4e2502 b4e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e42 b4e2502
        have b4e2520 : x = y := by
          first
          | (have i₁ := b4e2514
             have i₂ := b4e69
             grind)
          | exact superpose b4e69 b4e2514
          | exact resolve b4e2514 b4e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e69 b4e2514
        have b4e2574 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e2520
             grind)
          | exact superpose b4e2520 b4e18
          | exact resolve b4e18 b4e2520
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2520
        have b4e2587 : False := by grind
        exact b4e2587
      · have b5e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : y ≠ (M.op y x) := by grind
        have b5e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b5e20 : x ≠ (M.op x x) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e21 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b5e14 (σ x) (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e14
          | (have j0 := b5e14 (σ x) (σ y)
             grind)
          | (have r₁ := b5e14 (σ x) (σ y)
             have r₂ := b5e19
             grind)
          | exact resolve b5e14 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e22 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b5e21
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
        have b5e24 : (k x y) = (τ (σ x)) := by
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
        have b5e25 : x = (k x y) := by
          first
          | (have i₁ := b5e24
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e24
          | exact resolve b5e24 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24
        have b5e39 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b5e11 x X2 X4 X5
             have i₂ := b5e11 x X2 X0 X1
             grind)
          | exact superpose b5e11 b5e11
          | exact resolve b5e11 b5e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e41 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b5e11 X0 X1 (σ y) (σ x)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e11
          | exact resolve b5e11 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e62 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b5e25
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e25
          | (have j1 := b5e15 y x
             grind)
          | exact resolve b5e25 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25
        have b5e65 : x = (M.op x y) := by
          first
          | (have r₁ := b5e62
             have r₂ := b5e18
             grind)
          | exact resolve b5e62 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e62
        have b5e73 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b5e41 (σ y) (σ x)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e41
          | exact resolve b5e41 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e41
        have b5e108 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e39 X0 X1 X2 x y
             have i₂ := b5e65
             grind)
          | exact superpose b5e65 b5e39
          | exact resolve b5e39 b5e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e296 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b5e14 (σ y) (σ y)
             have i₂ := b5e73
             grind)
          | exact superpose b5e73 b5e14
          | (have j0 := b5e14 (σ y) (σ y)
             grind)
          | (have r₁ := b5e14 (σ y) (σ y)
             have r₂ := b5e73
             grind)
          | exact resolve b5e14 b5e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e73
        have b5e302 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b5e296
        have b5e303 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b5e302
             have i₂ := b5e16 y y
             grind)
          | exact superpose b5e16 b5e302
          | exact resolve b5e302 b5e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e302
        have b5e356 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b5e12 (k y y)
             have i₂ := b5e303
             grind)
          | exact superpose b5e303 b5e12
          | exact resolve b5e12 b5e303
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e303
        have b5e357 : y = (k y y) := by
          first
          | (have i₁ := b5e356
             have i₂ := b5e12 y
             grind)
          | exact superpose b5e12 b5e356
          | exact resolve b5e356 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e356
        have b5e535 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b5e15 y y
             have i₂ := b5e357
             grind)
          | exact superpose b5e357 b5e15
          | (have j0 := b5e15 y y
             grind)
          | exact resolve b5e15 b5e357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e357
        have b5e536 : y = (M.op y y) := by grind
        clear b5e535
        have b5e1077 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b5e39 X0 X1 X2 y y
             have i₂ := b5e536
             grind)
          | exact superpose b5e536 b5e39
          | exact resolve b5e39 b5e536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e39
        have b5e1087 : ∀ X2 : G, (M.op x X2) = (M.op y X2) := by
          intro X2
          first
          | (have i₁ := b5e1077 x x X2
             have i₂ := b5e108 x x X2
             grind)
          | exact superpose b5e108 b5e1077
          | exact resolve b5e1077 b5e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e108 b5e1077
        have b5e2296 : y = (M.op x y) := by
          first
          | (have i₁ := b5e536
             have i₂ := b5e1087 y
             grind)
          | exact superpose b5e1087 b5e536
          | exact resolve b5e536 b5e1087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e1087
        have b5e2297 : x = y := by
          first
          | (have i₁ := b5e2296
             have i₂ := b5e65
             grind)
          | exact superpose b5e65 b5e2296
          | exact resolve b5e2296 b5e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e65 b5e2296
        have b5e2370 : x = (M.op x x) := by
          first
          | (have i₁ := b5e536
             have i₂ := b5e2297
             grind)
          | exact superpose b5e2297 b5e536
          | exact resolve b5e536 b5e2297
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e536 b5e2297
        have b5e2374 : False := by grind
        exact b5e2374
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e18 : y ≠ (M.op y x) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e15 (σ X0) (σ X1)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 (σ X0) (σ X1)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1940 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e57 x y
             grind)
          | exact superpose b6e57 b6e19
          | (have j1 := b6e57 x y
             grind)
          | (have r₁ := b6e19
             have r₂ := b6e57 x y
             grind)
          | exact resolve b6e19 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e1963 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
        clear b6e1940
        have b6e2037 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e1963
             grind)
          | exact superpose b6e1963 b6e17
          | exact resolve b6e17 b6e1963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1963
        have b6e2118 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e2037
             have i₂ := b6e15 x y
             grind)
          | exact superpose b6e15 b6e2037
          | (have j1 := b6e15 x y
             grind)
          | exact resolve b6e2037 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2037
        have b6e2119 : y = (M.op y x) := by grind
        clear b6e2118
        have b6e2120 : False := by grind
        exact b6e2120
      · have b7e15 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op y x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X0 X1
             have i₂ := b7e15 (σ X0) (σ X1)
             grind)
          | exact superpose b7e15 b7e16
          | (have j1 := b7e15 (σ X0) (σ X1)
             grind)
          | exact resolve b7e16 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e605 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b7e19
             have i₂ := b7e46 x y
             grind)
          | exact superpose b7e46 b7e19
          | (have j1 := b7e46 x y
             grind)
          | (have r₁ := b7e19
             have r₂ := b7e46 x y
             grind)
          | exact resolve b7e19 b7e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46
        have b7e627 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
        clear b7e605
        have b7e667 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e627
             grind)
          | exact superpose b7e627 b7e17
          | exact resolve b7e17 b7e627
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e627
        have b7e687 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b7e667
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e667
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e667 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e667
        have b7e688 : y = (M.op y x) := by grind
        clear b7e687
        have b7e689 : False := by grind
        exact b7e689

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4428 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
        intro X0 X1 X2 X3
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
      have b0e28 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e10 (M.op X2 X3) X1 X4 X5
           have i₂ := b0e10 X0 X1 X2 X3
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 (σ y) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1 y y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
        intro X1
        first
        | (have i₁ := b0e34 x X1
           have i₂ := b0e35 x X1
           grind)
        | exact superpose b0e35 b0e34
        | exact resolve b0e34 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e41 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X1) = (M.op (M.op X2 X3) (M.op y X1)) := by
        intro X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e28 x X1 X2 X3 X4 X5
           have i₂ := b0e35 x X1
           grind)
        | exact superpose b0e35 b0e28
        | exact resolve b0e28 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e44 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e39 (σ y)
           grind)
        | exact superpose b0e39 b0e18
        | exact resolve b0e18 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
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
      have b0e58 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X0 X0
           have i₂ := b0e14 X3 X0
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X3 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
      have b0e65 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e57 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e67 : ∀ X0 X2 X3 : G, (M.op y X2) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X0 X3) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e58 X0 x X2 X3
           have i₂ := b0e35 x X2
           grind)
        | exact superpose b0e35 b0e58
        | (have j0 := b0e58 X0 x X2 X3
           grind)
        | exact resolve b0e58 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e82 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op X2 X3) X0) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e10 x X0 X2 X3
           have i₂ := b0e35 x X0
           grind)
        | exact superpose b0e35 b0e10
        | exact resolve b0e10 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e134 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e467 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e65 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e65 b0e15
        | (have j1 := b0e65 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e474 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e65 X0 X2 (τ X1)
           grind)
        | exact superpose b0e65 b0e23
        | (have j1 := b0e65 X0 X2 X2
           grind)
        | exact resolve b0e23 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e65
      have b0e571 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op y X2) ∨ (k X3 (M.op y X2)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e13 X3 (M.op y X2)
           have i₂ := b0e41 X2 y X2 X0 X1
           grind)
        | exact superpose b0e41 b0e13
        | (have j0 := b0e13 X3 (M.op y X2)
           grind)
        | exact resolve b0e13 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e585 : ∀ X2 X3 : G, (k X3 (M.op y X2)) = X3 := by
        intro X2 X3
        first
        | (have j0 := b0e571 x x X2 X3
           grind)
        | (have r₁ := b0e571 X2 X3 x X3
           have r₂ := b0e82 x X2 X3
           grind)
        | exact resolve b0e571 b0e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e571
      have b0e776 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e67 (σ x) (σ y) X0
           grind)
        | exact superpose b0e67 b0e16
        | (have j1 := b0e67 (σ x) x X0
           grind)
        | exact resolve b0e16 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e787 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e776 X0
           have i₂ := b0e44
           grind)
        | exact superpose b0e44 b0e776
        | (have j0 := b0e776 X0
           grind)
        | exact resolve b0e776 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e776
      have b0e2262 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 X1 (σ X0)
           have i₂ := b0e62 X0 X0
           grind)
        | exact superpose b0e62 b0e13
        | (have j0 := b0e13 X1 (σ X0)
           have j1 := b0e62 X0 X1
           grind)
        | (have r₁ := b0e13 X0 (σ X0)
           have r₂ := b0e62 X0 X1
           grind)
        | exact resolve b0e13 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2304 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e62 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e2334 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e2262 X0 X1
           have j1 := b0e13 X1 (σ X0)
           grind)
        | (have r₁ := b0e2262 X0 X1
           have r₂ := b0e13 X0 (σ X0)
           grind)
        | exact resolve b0e2262 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2262
      have b0e4807 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e474 X1 (σ X0) X2
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e474
        | (have j0 := b0e474 X1 X1 X2
           grind)
        | exact resolve b0e474 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e474
      have b0e4898 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e4807 X0 X1 X2
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e4807
        | (have j0 := b0e4807 X0 X1 X2
           grind)
        | exact resolve b0e4807 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4807
      have b0e5592 : ∀ X0 : G, (σ (M.op y X0)) ≠ (σ (M.op y X0)) ∨ (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
        intro X0
        first
        | (have i₁ := b0e2304 (M.op y X0)
           have i₂ := b0e585 X0 (M.op y X0)
           grind)
        | exact superpose b0e585 b0e2304
        | (have j0 := b0e2304 (M.op y X0)
           grind)
        | exact resolve b0e2304 b0e585
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e585
      have b0e5622 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e2304 (τ X0)
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e2304
        | (have j0 := b0e2304 (τ X0)
           grind)
        | exact resolve b0e2304 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e2304
      have b0e5648 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
        intro X0
        first
        | (have j0 := b0e5592 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5592
      have b0e5651 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e5622 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e5622
        | (have j0 := b0e5622 X0
           grind)
        | exact resolve b0e5622 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5622
      have b0e5666 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e5651 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e5651
        | (have j0 := b0e5651 X0
           grind)
        | exact resolve b0e5651 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5651
      have b0e6357 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ (k X2 X1)) = (M.op (σ X1) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e134 X0 (σ X1)
           have i₂ := b0e467 X1 X2 (σ X0)
           grind)
        | exact superpose b0e467 b0e134
        | (have j1 := b0e467 X1 X2 X2
           grind)
        | exact resolve b0e134 b0e467
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134 b0e467
      have b0e6364 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X2 X1)) = (M.op (σ X1) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e6357 X0 X1 X2
           have i₂ := b0e11 X1
           grind)
        | exact superpose b0e11 b0e6357
        | (have j0 := b0e6357 X0 X1 X2
           grind)
        | exact resolve b0e6357 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6357
      have b0e6395 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X2 X1)) = (M.op (σ X1) (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e6364 X0 X1 X2
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e6364
        | (have j0 := b0e6364 X0 X1 X2
           grind)
        | exact resolve b0e6364 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6364
      have b0e34113 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op y X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e82 X1 (σ (M.op y X0)) (σ (M.op y X0))
           have i₂ := b0e5648 X0
           grind)
        | exact superpose b0e5648 b0e82
        | exact resolve b0e82 b0e5648
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5648
      have b0e41951 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e6395 X0 x y
           grind)
        | exact superpose b0e6395 b0e16
        | (have j1 := b0e6395 X0 x x
           grind)
        | exact resolve b0e16 b0e6395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6395
      have b0e42087 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e41951 X0
           have j1 := b0e4898 X0 x X0
           grind)
        | (have r₁ := b0e41951 X0
           have r₂ := b0e4898 y x x
           grind)
        | exact resolve b0e41951 b0e4898
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4898 b0e41951
      have b0e42165 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e5666 x
           have i₂ := b0e42087 x
           grind)
        | exact superpose b0e42087 b0e5666
        | (have j0 := b0e5666 x
           grind)
        | (have r₁ := b0e5666 x
           have r₂ := b0e42087 x
           grind)
        | exact resolve b0e5666 b0e42087
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5666
      have b0e42168 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2334 x X0
           have i₂ := b0e42087 x
           grind)
        | exact superpose b0e42087 b0e2334
        | (have j0 := b0e2334 x X0
           grind)
        | exact resolve b0e2334 b0e42087
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2334 b0e42087
      have b0e42218 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have j0 := b0e42168 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42168
      have b0e42221 : x = (M.op x x) := by grind
      clear b0e42165
      have b0e42759 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e82 X0 x x
           have i₂ := b0e42221
           grind)
        | exact superpose b0e42221 b0e82
        | exact resolve b0e82 b0e42221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45007 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e787 X0
           have i₂ := b0e42759 y
           grind)
        | exact superpose b0e42759 b0e787
        | (have j0 := b0e787 X0
           grind)
        | exact resolve b0e787 b0e42759
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e787
      have b0e45008 : x = (M.op y x) := by
        first
        | (have i₁ := b0e42221
           have i₂ := b0e42759 x
           grind)
        | exact superpose b0e42759 b0e42221
        | exact resolve b0e42221 b0e42759
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42221 b0e42759
      have b0e45195 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e45007 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e45007
        | (have j0 := b0e45007 X0
           grind)
        | exact resolve b0e45007 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45007
      have b0e45196 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e45195 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45195
      have b0e45233 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e45196 X0
           have i₂ := b0e42218 X0
           grind)
        | exact superpose b0e42218 b0e45196
        | exact resolve b0e45196 b0e42218
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42218 b0e45196
      have b0e45785 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e34113 x X0
           have i₂ := b0e45008
           grind)
        | exact superpose b0e45008 b0e34113
        | exact resolve b0e34113 b0e45008
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34113 b0e45008
      have b0e45850 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e45785 X0
           have i₂ := b0e45233 X0
           grind)
        | exact superpose b0e45233 b0e45785
        | exact resolve b0e45785 b0e45233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45233 b0e45785
      have b0e46660 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e82 X1 y X0
           have i₂ := b0e45850 X0
           grind)
        | exact superpose b0e45850 b0e82
        | exact resolve b0e82 b0e45850
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82
      have b0e46823 : ∀ X0 X1 : G, (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e46660 X0 X1
           have i₂ := b0e45850 X1
           grind)
        | exact superpose b0e45850 b0e46660
        | exact resolve b0e46660 b0e45850
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45850 b0e46660
      have b0e48172 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e46823 (σ x) (σ y)
           grind)
        | exact superpose b0e46823 b0e16
        | exact resolve b0e16 b0e46823
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48249 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e48172
           have i₂ := b0e46823 x y
           grind)
        | exact superpose b0e46823 b0e48172
        | exact resolve b0e48172 b0e46823
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46823 b0e48172
      have b0e48250 : False := by grind
      exact b0e48250
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
      have b1e55 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
      have b1e59 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e55 X0
           grind)
        | (have r₁ := b1e55 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e55 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e55 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e66 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e59 (σ y)
           grind)
        | exact superpose b1e59 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e59 (σ y)
           grind)
        | exact resolve b1e18 b1e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59
      have b1e72 : False := by grind
      exact b1e72
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
      have b2e54 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
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
      have b2e58 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e54 X0
           grind)
        | (have r₁ := b2e54 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e54 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e54 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54
      have b2e63 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e58 y
           grind)
        | exact superpose b2e58 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e58 y
           grind)
        | exact resolve b2e17 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58
      have b2e67 : False := by grind
      exact b2e67
    · have b3e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
        intro X0 X1 X2 X3
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
      have b3e23 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
        intro X0 X1 X2 X4 X5
        first
        | (have i₁ := b3e10 x X2 X4 X5
           have i₂ := b3e10 x X2 X0 X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e27 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e10 X0 X1 x x
           have i₂ := b3e10 X2 X1 x x
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b3e36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
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
      have b3e40 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
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
      have b3e41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
      have b3e42 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 X0 X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e43 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have j0 := b3e40 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40
      have b3e44 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e36 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e46 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e43 (σ X0)
           grind)
        | exact superpose b3e43 b3e15
        | exact resolve b3e15 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e57 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e33 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e33
        | exact resolve b3e33 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e61 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
        intro X0
        first
        | (have i₁ := b3e33 X0 y
           have i₂ := b3e43 X0
           grind)
        | exact superpose b3e43 b3e33
        | exact resolve b3e33 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e98 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 X6) X4) = (M.op (M.op X0 X1) (M.op (M.op X2 X3) X4)) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b3e10 (M.op X2 X3) X4 X5 X6
           have i₂ := b3e23 X2 X3 (M.op (M.op X2 X3) X4) X0 X1
           grind)
        | (have i₁ := b3e10 (M.op X2 X3) X4 X5 X6
           have i₂ := b3e23 X0 X1 (M.op (M.op X2 X3) X4) X2 X3
           grind)
        | exact superpose b3e23 b3e10
        | exact resolve b3e10 b3e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e103 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e46 y
           grind)
        | exact superpose b3e46 b3e18
        | exact resolve b3e18 b3e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e46
      have b3e173 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e103
           have i₂ := b3e44 y y X0
           grind)
        | exact superpose b3e44 b3e103
        | (have j1 := b3e44 y x X0
           grind)
        | exact resolve b3e103 b3e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e103
      have b3e176 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e44 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b3e44 b3e15
        | (have j1 := b3e44 (σ X0) X2 X2
           grind)
        | exact resolve b3e15 b3e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44
      have b3e180 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b3e173 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e173
      have b3e273 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e180 (τ X0)
           grind)
        | exact superpose b3e180 b3e19
        | exact resolve b3e19 b3e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e275 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e273 X0
           have i₂ := b3e43 X0
           grind)
        | exact superpose b3e43 b3e273
        | exact resolve b3e273 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e43 b3e273
      have b3e972 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e13 X1 (σ X0)
           have i₂ := b3e41 X0 X0
           grind)
        | exact superpose b3e41 b3e13
        | (have j0 := b3e13 X1 (σ X0)
           have j1 := b3e41 X0 X1
           grind)
        | (have r₁ := b3e13 X0 (σ X0)
           have r₂ := b3e41 X0 X1
           grind)
        | exact resolve b3e13 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1019 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e41 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e41
      have b3e1024 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b3e972 X0 X1
           have j1 := b3e13 X1 (σ X0)
           grind)
        | (have r₁ := b3e972 X0 X1
           have r₂ := b3e13 X0 (σ X0)
           grind)
        | exact resolve b3e972 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e972
      have b3e1034 : ∀ X0 X1 : G, (k (τ (M.op (σ y) X1)) y) = (τ (M.op X0 (M.op X0 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e61 (M.op (σ y) X1)
           have i₂ := b3e27 (σ y) X1 X0
           grind)
        | (have i₁ := b3e61 (M.op (σ y) X1)
           have i₂ := b3e27 X0 X1 (σ y)
           grind)
        | exact superpose b3e27 b3e61
        | exact resolve b3e61 b3e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1035 : ∀ X0 X1 X2 : G, (k (τ (M.op (σ y) X2)) y) = (τ (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e61 (M.op (σ y) X2)
           have i₂ := b3e10 (σ y) X2 X0 X1
           grind)
        | exact superpose b3e10 b3e61
        | exact resolve b3e61 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1051 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (M.op y (τ (M.op (σ y) X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1035 X0 X1 X2
           have i₂ := b3e180 (τ (M.op (σ y) X2))
           grind)
        | exact superpose b3e180 b3e1035
        | exact resolve b3e1035 b3e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1035
      have b3e1052 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op y (τ (M.op (σ y) X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e1034 X0 X1
           have i₂ := b3e180 (τ (M.op (σ y) X1))
           grind)
        | exact superpose b3e180 b3e1034
        | exact resolve b3e1034 b3e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1034
      have b3e1058 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (M.op y (k (τ X2) y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1051 X0 X1 X2
           have i₂ := b3e61 X2
           grind)
        | exact superpose b3e61 b3e1051
        | exact resolve b3e1051 b3e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1051
      have b3e1059 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op y (k (τ X1) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e1052 X0 X1
           have i₂ := b3e61 X1
           grind)
        | exact superpose b3e61 b3e1052
        | exact resolve b3e1052 b3e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e61 b3e1052
      have b3e1065 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) X2)) = (M.op y (M.op y (τ X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1058 X0 X1 X2
           have i₂ := b3e180 (τ X2)
           grind)
        | exact superpose b3e180 b3e1058
        | exact resolve b3e1058 b3e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1058
      have b3e1066 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op y (M.op y (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e1059 X0 X1
           have i₂ := b3e180 (τ X1)
           grind)
        | exact superpose b3e180 b3e1059
        | exact resolve b3e1059 b3e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e180 b3e1059
      have b3e1439 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1024 (τ X0) X1
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e1024
        | (have j0 := b3e1024 (τ X0) X1
           grind)
        | exact resolve b3e1024 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1024
      have b3e1447 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1439 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1439
        | (have j0 := b3e1439 X0 X1
           grind)
        | exact resolve b3e1439 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1439
      have b3e1451 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1447 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1447
        | (have j0 := b3e1447 X0 X1
           grind)
        | exact resolve b3e1447 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1447
      have b3e1727 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1451 (τ X0) X1
           have i₂ := b3e57 X0 X0
           grind)
        | exact superpose b3e57 b3e1451
        | (have j0 := b3e1451 (τ X0) X1
           grind)
        | exact resolve b3e1451 b3e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e57 b3e1451
      have b3e1737 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e42 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e42
        | (have j0 := b3e42 X1 X1
           grind)
        | exact resolve b3e42 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42
      have b3e1835 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e1737 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e1737
        | (have j0 := b3e1737 X0 X1
           grind)
        | exact resolve b3e1737 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1737
      have b3e1838 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e275 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e275
        | exact resolve b3e275 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e275
      have b3e2071 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (σ (M.op y X0)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e23 X1 X2 X3 (σ y) (σ X0)
           have i₂ := b3e1838 X0
           grind)
        | exact superpose b3e1838 b3e23
        | exact resolve b3e23 b3e1838
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1838
      have b3e8234 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e1019 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e1019
        | (have j0 := b3e1019 (τ X0)
           grind)
        | exact resolve b3e1019 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e8253 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e8234 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e8234
        | (have j0 := b3e8234 X0
           grind)
        | exact resolve b3e8234 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e8234
      have b3e8261 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e8253 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e8253
        | (have j0 := b3e8253 X0
           grind)
        | exact resolve b3e8253 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e8253
      have b3e10008 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e176 x y X0
           grind)
        | exact superpose b3e176 b3e16
        | (have j1 := b3e176 x x X0
           grind)
        | exact resolve b3e16 b3e176
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e176
      have b3e26182 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (σ (M.op y (M.op y (τ X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e12 (M.op (M.op X1 X2) X0)
           have i₂ := b3e1065 X1 X2 X0
           grind)
        | exact superpose b3e1065 b3e12
        | exact resolve b3e12 b3e1065
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1065
      have b3e27710 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (σ (M.op y (M.op y (τ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b3e12 (M.op X1 (M.op X1 X0))
           have i₂ := b3e1066 X1 X0
           grind)
        | exact superpose b3e1066 b3e12
        | exact resolve b3e12 b3e1066
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1066
      have b3e48898 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e26182 X1 X2 X3
           have i₂ := b3e27 y (τ X1) X0
           grind)
        | (have i₁ := b3e26182 X1 X2 X3
           have i₂ := b3e27 X0 (τ X1) y
           grind)
        | exact superpose b3e27 b3e26182
        | exact resolve b3e26182 b3e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26182
      have b3e51806 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e27710 X1 X2
           have i₂ := b3e27 y (τ X1) X0
           grind)
        | (have i₁ := b3e27710 X1 X2
           have i₂ := b3e27 X0 (τ X1) y
           grind)
        | exact superpose b3e27 b3e27710
        | exact resolve b3e27710 b3e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27 b3e27710
      have b3e61173 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (σ X0)) = (σ (M.op X3 (M.op X3 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e48898 X3 (σ X0) X1 X2
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e48898
        | exact resolve b3e48898 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e61334 : ∀ X0 X1 X4 : G, (σ (M.op X0 (M.op X0 (τ X1)))) = (M.op (σ (M.op y X4)) X1) := by
        intro X0 X1 X4
        first
        | (have i₁ := b3e2071 X4 x x X1
           have i₂ := b3e48898 X0 X1 x x
           grind)
        | exact superpose b3e48898 b3e2071
        | exact resolve b3e2071 b3e48898
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2071 b3e48898
      have b3e65015 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e11 (M.op X2 (M.op X2 (τ X1)))
           have i₂ := b3e51806 X2 X1 X0
           grind)
        | exact superpose b3e51806 b3e11
        | exact resolve b3e11 b3e51806
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e51806
      have b3e84522 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (M.op X3 X4) (σ X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e61173 X2 X3 X4 (M.op x x)
           have i₂ := b3e98 x x x x X2 X0 X1
           grind)
        | exact superpose b3e98 b3e61173
        | exact resolve b3e61173 b3e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e98 b3e61173
      have b3e452538 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e10008 X0
           have i₂ := b3e1835 y x
           grind)
        | exact superpose b3e1835 b3e10008
        | (have j0 := b3e10008 X0
           have j1 := b3e1835 X0 x
           grind)
        | (have r₁ := b3e10008 X0
           have r₂ := b3e1835 y x
           grind)
        | exact resolve b3e10008 b3e1835
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1835 b3e10008
      have b3e452540 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e452538 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e452538
      have b3e453851 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e1727 (σ x) X0
           have i₂ := b3e452540 (σ x)
           grind)
        | exact superpose b3e452540 b3e1727
        | (have j0 := b3e1727 (σ x) X0
           grind)
        | exact resolve b3e1727 b3e452540
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1727 b3e452540
      have b3e453885 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e453851 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e453851
      have b3e453900 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e453885 X0
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e453885
        | exact resolve b3e453885 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e453885
      have b3e453912 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e453900 X0
           have j1 := b3e13 X0 x
           grind)
        | (have r₁ := b3e453900 X0
           have r₂ := b3e13 X0 x
           grind)
        | exact resolve b3e453900 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e453900
      have b3e454813 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e8261 x
           have i₂ := b3e453912 x
           grind)
        | exact superpose b3e453912 b3e8261
        | (have j0 := b3e8261 x
           grind)
        | (have r₁ := b3e8261 x
           have r₂ := b3e453912 x
           grind)
        | exact resolve b3e8261 b3e453912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e8261
      have b3e454814 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e1019 x
           have i₂ := b3e453912 x
           grind)
        | exact superpose b3e453912 b3e1019
        | (have j0 := b3e1019 x
           grind)
        | exact resolve b3e1019 b3e453912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1019 b3e453912
      have b3e454877 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e454814
      have b3e454878 : x = (M.op x x) := by grind
      clear b3e454813
      have b3e455753 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X0 X1 x x
           have i₂ := b3e454878
           grind)
        | exact superpose b3e454878 b3e10
        | exact resolve b3e10 b3e454878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e455760 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e23 X0 X1 X2 x x
           have i₂ := b3e454878
           grind)
        | exact superpose b3e454878 b3e23
        | exact resolve b3e23 b3e454878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e456010 : ∀ X0 : G, (τ (M.op x x)) = (M.op X0 (M.op X0 (τ x))) := by
        intro X0
        first
        | (have i₁ := b3e65015 x x X0
           have i₂ := b3e454878
           grind)
        | exact superpose b3e454878 b3e65015
        | exact resolve b3e65015 b3e454878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e65015
      have b3e456036 : ∀ X0 : G, (τ x) = (M.op X0 (M.op X0 (τ x))) := by
        intro X0
        first
        | (have i₁ := b3e456010 X0
           have i₂ := b3e454878
           grind)
        | exact superpose b3e454878 b3e456010
        | exact resolve b3e456010 b3e454878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e454878 b3e456010
      have b3e456114 : (τ x) = (M.op x (τ x)) := by
        first
        | (have i₁ := b3e456036 x
           have i₂ := b3e455753 x (τ x)
           grind)
        | exact superpose b3e455753 b3e456036
        | exact resolve b3e456036 b3e455753
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e455753 b3e456036
      have b3e481412 : ∀ X0 : G, (M.op (σ (M.op y X0)) x) = (σ (M.op x (τ x))) := by
        intro X0
        first
        | (have i₁ := b3e61334 x x X0
           have i₂ := b3e456114
           grind)
        | exact superpose b3e456114 b3e61334
        | exact resolve b3e61334 b3e456114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e61334
      have b3e481794 : ∀ X0 : G, (M.op (σ (M.op y X0)) x) = (σ (τ x)) := by
        intro X0
        first
        | (have i₁ := b3e481412 X0
           have i₂ := b3e456114
           grind)
        | exact superpose b3e456114 b3e481412
        | exact resolve b3e481412 b3e456114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e456114 b3e481412
      have b3e481885 : ∀ X0 : G, x = (M.op (σ (M.op y X0)) x) := by
        intro X0
        first
        | (have i₁ := b3e481794 X0
           have i₂ := b3e12 x
           grind)
        | exact superpose b3e12 b3e481794
        | exact resolve b3e481794 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e481794
      have b3e482157 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ x) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e23 X0 X1 X2 (σ x) (σ x)
           have i₂ := b3e454877
           grind)
        | exact superpose b3e454877 b3e23
        | exact resolve b3e23 b3e454877
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e23 b3e454877
      have b3e482537 : ∀ X2 : G, (M.op (σ x) X2) = (M.op x X2) := by
        intro X2
        first
        | (have i₁ := b3e482157 x x X2
           have i₂ := b3e455760 x x X2
           grind)
        | exact superpose b3e455760 b3e482157
        | exact resolve b3e482157 b3e455760
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e482157
      have b3e486834 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e482537 (σ y)
           grind)
        | exact superpose b3e482537 b3e16
        | exact resolve b3e16 b3e482537
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e482537
      have b3e491746 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op x (σ X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e84522 X0 X1 X2 (σ (M.op y x)) x
           have i₂ := b3e481885 x
           grind)
        | exact superpose b3e481885 b3e84522
        | exact resolve b3e84522 b3e481885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e84522 b3e481885
      have b3e491770 : ∀ X2 : G, (σ (M.op x X2)) = (M.op x (σ X2)) := by
        intro X2
        first
        | (have i₁ := b3e491746 x x X2
           have i₂ := b3e455760 x x X2
           grind)
        | exact superpose b3e455760 b3e491746
        | exact resolve b3e491746 b3e455760
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e455760 b3e491746
      have b3e503747 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b3e486834
           have i₂ := b3e491770 y
           grind)
        | exact superpose b3e491770 b3e486834
        | (have r₁ := b3e486834
           have r₂ := b3e491770 y
           grind)
        | exact resolve b3e486834 b3e491770
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e486834 b3e491770
      have b3e503835 : False := by grind
      exact b3e503835

/-- `Equation4434`: `x ◇ (y ◇ x) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4434 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4434 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
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
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b0e29 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ y) (σ y) x
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 y y x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e10 X0 x X3
           have i₂ := b0e10 X0 x X1
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X0 X1 x
           have i₂ := b0e10 X0 X2 x
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e30 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e30
        | exact resolve b0e30 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e40 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e29
        | exact resolve b0e29 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e53 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
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
      have b0e54 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X1 X2
           have i₂ := b0e14 X0 X1
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e14 (σ X0) (σ X1)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 X0 (σ X1)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e53 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e63 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (σ y) X1
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e10
        | exact resolve b0e10 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e99 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k (τ X0) X1)
           have i₂ := b0e23 X0 X1
           grind)
        | exact superpose b0e23 b0e11
        | exact resolve b0e11 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e212 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X0 X1 (σ y)
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e36
        | exact resolve b0e36 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e215 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X0 X1 y
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e36
        | exact resolve b0e36 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e39
      have b0e247 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e212 X0 x
           have i₂ := b0e215 X0 x
           grind)
        | exact superpose b0e215 b0e212
        | exact resolve b0e212 b0e215
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e212
      have b0e299 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e247 (σ x)
           grind)
        | exact superpose b0e247 b0e16
        | exact resolve b0e16 b0e247
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e388 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op X0 y) := by
        intro X0 X2
        first
        | (have i₁ := b0e10 X0 x X2
           have i₂ := b0e215 X0 x
           grind)
        | exact superpose b0e215 b0e10
        | exact resolve b0e10 b0e215
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e215
      have b0e833 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 X2 X0
           have i₂ := b0e54 X0 X1 X3
           grind)
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e54 X1 X1 X2
           grind)
        | exact superpose b0e54 b0e14
        | (have j0 := b0e14 X2 X0
           have j1 := b0e54 X0 X1 X2
           grind)
        | exact resolve b0e14 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e2326 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (σ X0) X2) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e31 (σ X1) X1 X3
           have i₂ := b0e56 X0 X1
           grind)
        | exact superpose b0e56 b0e31
        | (have j1 := b0e56 X3 X0
           grind)
        | exact resolve b0e31 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31 b0e56
      have b0e3374 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e99 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e99
        | exact resolve b0e99 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99
      have b0e16600 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e833 X1 X2 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e833
      have b0e16601 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e16600 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16600
      have b0e18353 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e2326 X0 X1 x X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2326
      have b0e166293 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) ≠ (M.op (σ (τ X0)) X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e18353 (τ X0) X1
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e18353
        | exact resolve b0e18353 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e18353
      have b0e166513 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e166293 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e166293
        | (have j0 := b0e166293 X0 X1
           grind)
        | exact resolve b0e166293 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e166293
      have b0e166526 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e166513 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e166513
        | (have j0 := b0e166513 X0 X1
           grind)
        | exact resolve b0e166513 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e166513
      have b0e166559 : ∀ X0 X2 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e166526 X0 x
           have i₂ := b0e16601 X2 X0 x
           grind)
        | exact superpose b0e16601 b0e166526
        | (have j0 := b0e166526 X0 x
           have j1 := b0e16601 X0 X0 X2
           grind)
        | (have r₁ := b0e166526 x x
           have r₂ := b0e16601 x x X2
           grind)
        | exact resolve b0e166526 b0e16601
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16601 b0e166526
      have b0e166728 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X2
        first
        | (have j0 := b0e166559 X0 X0
           have j1 := b0e59 X0 x X0
           grind)
        | (have r₁ := b0e166559 X0 X2
           have r₂ := b0e59 X0 X0 X2
           grind)
        | exact resolve b0e166559 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e166559
      have b0e169011 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e166728 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e166728
      have b0e169012 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e169011 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e169011
      have b0e170424 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e3374 X0 X0
           have i₂ := b0e169012 (τ X0)
           grind)
        | exact superpose b0e169012 b0e3374
        | exact resolve b0e3374 b0e169012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3374
      have b0e170453 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
        intro X0
        first
        | (have i₁ := b0e170424 X0
           have i₂ := b0e169012 X0
           grind)
        | exact superpose b0e169012 b0e170424
        | exact resolve b0e170424 b0e169012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e169012 b0e170424
      have b0e171241 : ∀ X0 X1 : G, (M.op (τ X0) y) = (M.op (τ (M.op X0 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e388 (τ X0) X1
           have i₂ := b0e170453 X0
           grind)
        | exact superpose b0e170453 b0e388
        | exact resolve b0e388 b0e170453
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e388
      have b0e174295 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e170453 (M.op X0 X0)
           have i₂ := b0e171241 X0 (τ (M.op X0 X0))
           grind)
        | exact superpose b0e171241 b0e170453
        | exact resolve b0e170453 b0e171241
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170453 b0e171241
      have b0e174584 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (M.op (τ X0) y) := by
        intro X0
        first
        | (have i₁ := b0e174295 X0
           have i₂ := b0e63 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e63 b0e174295
        | exact resolve b0e174295 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63 b0e174295
      have b0e174772 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ X0) y) := by
        intro X0
        first
        | (have i₁ := b0e174584 X0
           have i₂ := b0e247 X0
           grind)
        | exact superpose b0e247 b0e174584
        | exact resolve b0e174584 b0e247
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e247 b0e174584
      have b0e175577 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
        intro X0
        first
        | (have i₁ := b0e12 (M.op X0 y)
           have i₂ := b0e174772 X0
           grind)
        | exact superpose b0e174772 b0e12
        | exact resolve b0e12 b0e174772
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e174772
      have b0e176926 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
        intro X0
        first
        | (have i₁ := b0e175577 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e175577
        | exact resolve b0e175577 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e175577
      have b0e178411 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e299
           have i₂ := b0e176926 x
           grind)
        | exact superpose b0e176926 b0e299
        | (have r₁ := b0e299
           have r₂ := b0e176926 x
           grind)
        | exact resolve b0e299 b0e176926
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e299 b0e176926
      have b0e178516 : False := by grind
      exact b0e178516
    · have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b1e54 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e18
           have i₂ := b1e14 X0 (σ y)
           grind)
        | exact superpose b1e14 b1e18
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e14 X0 (σ y)
           grind)
        | exact resolve b1e18 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e58 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b1e54 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e60 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e58 X0
           have i₂ := b1e28 X0
           grind)
        | exact superpose b1e28 b1e58
        | exact resolve b1e58 b1e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28 b1e58
      have b1e66 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e60 (σ y)
           grind)
        | exact superpose b1e60 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e60 (σ y)
           grind)
        | exact resolve b1e18 b1e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e60
      have b1e68 : False := by grind
      exact b1e68
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b2e52 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
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
      have b2e56 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b2e52 X0
           grind)
        | (have r₁ := b2e52 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e52 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e52 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e63 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e56 y
           grind)
        | exact superpose b2e56 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e56 y
           grind)
        | exact resolve b2e17 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56
      have b2e64 : False := by grind
      exact b2e64
    · have b3e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
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
      have b3e39 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
      have b3e42 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b3e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39
      have b3e43 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e36 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e45 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e42 (σ X0)
           grind)
        | exact superpose b3e42 b3e15
        | exact resolve b3e15 b3e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42
      have b3e96 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e45 y
           grind)
        | exact superpose b3e45 b3e18
        | exact resolve b3e18 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e97 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e45 x
           grind)
        | exact superpose b3e45 b3e16
        | exact resolve b3e16 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e45
      have b3e158 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b3e96
           have i₂ := b3e43 y y X0
           grind)
        | exact superpose b3e43 b3e96
        | (have j1 := b3e43 y x X0
           grind)
        | exact resolve b3e96 b3e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e43 b3e96
      have b3e165 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b3e158 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e158
      have b3e296 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b3e97
           have i₂ := b3e165 x
           grind)
        | exact superpose b3e165 b3e97
        | exact resolve b3e97 b3e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e97 b3e165
      have b3e304 : False := by grind
      exact b3e304

/-- `Equation4437`: `x ◇ (y ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4437 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4437 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
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
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
        intro X0 X1 X2
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
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
      have b1e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 X1 X3
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b1e76 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      clear b1e22
      have b1e110 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      clear b1e23
      have b1e301 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e76 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e76
        | exact resolve b1e76 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e305 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e76 X0 X1
           have i₂ := b1e14 X0 (σ X1)
           grind)
        | exact superpose b1e14 b1e76
        | (have j1 := b1e14 X0 (σ X1)
           grind)
        | exact resolve b1e76 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e76
      have b1e821 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) X2) = (M.op (σ (k X0 X1)) X3) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e26 (σ X0) (σ X1) X2 X3
           have i₂ := b1e52 X0 X1
           grind)
        | exact superpose b1e52 b1e26
        | (have j1 := b1e52 X0 X1
           grind)
        | exact resolve b1e26 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e829 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e52 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52
      have b1e11834 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e829 (τ X0) (τ X1)
           have i₂ := b1e301 X1 X0
           grind)
        | exact superpose b1e301 b1e829
        | (have j0 := b1e829 (τ X0) (τ X1)
           grind)
        | exact resolve b1e829 b1e301
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e301
      have b1e11837 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e829 x y
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e829
        | (have j0 := b1e829 x y
           grind)
        | exact resolve b1e829 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e829
      have b1e11856 : (σ x) ≠ (σ y) := by
        first
        | (have r₁ := b1e11837
           have r₂ := b1e18
           grind)
        | exact resolve b1e11837 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11837
      have b1e11857 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11834 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e11834
        | (have j0 := b1e11834 X0 X1
           grind)
        | exact resolve b1e11834 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11834
      have b1e11863 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e11857 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e11857
        | (have j0 := b1e11857 X0 X1
           grind)
        | exact resolve b1e11857 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11857
      have b1e11864 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e11863 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e11863
        | (have j0 := b1e11863 X0 X1
           grind)
        | exact resolve b1e11863 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11863
      have b1e11865 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e11864 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e11864
        | (have j0 := b1e11864 X0 X1
           grind)
        | exact resolve b1e11864 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11864
      have b1e97773 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e821 x y x x
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e821
        | (have j0 := b1e821 x y x x
           grind)
        | exact resolve b1e821 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e821
      have b1e98409 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have j0 := b1e97773 X0 X1
           grind)
        | (have r₁ := b1e97773 X0 X1
           have r₂ := b1e18
           grind)
        | exact resolve b1e97773 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e97773
      have b1e98805 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ X1 ∨ (σ x) = (k (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e13 (σ x) X1
           have i₂ := b1e98409 X0 X1
           grind)
        | (have i₁ := b1e13 (σ x) X1
           have i₂ := b1e98409 X1 X0
           grind)
        | exact superpose b1e98409 b1e13
        | (have j0 := b1e13 (σ x) X1
           grind)
        | (have r₁ := b1e13 (σ x) (M.op (σ x) X0)
           have r₂ := b1e98409 X0 (M.op (σ x) X0)
           grind)
        | (have r₁ := b1e13 (σ x) (M.op (σ x) X1)
           have r₂ := b1e98409 (M.op (σ x) X1) X1
           grind)
        | exact resolve b1e13 b1e98409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e98409
      have b1e194135 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) := by
        intro X0
        first
        | (have j0 := b1e98805 X0 (M.op (σ x) X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e98805
      have b1e194500 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (σ x) X0))) := by
        intro X0
        first
        | (have i₁ := b1e110 x (M.op (σ x) X0)
           have i₂ := b1e194135 X0
           grind)
        | exact superpose b1e194135 b1e110
        | exact resolve b1e110 b1e194135
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e110 b1e194135
      have b1e194516 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
        intro X0
        first
        | (have i₁ := b1e194500 X0
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e194500
        | exact resolve b1e194500 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e194500
      have b1e197183 : ∀ X0 : G, x = (k x (k (τ (σ x)) X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e194516 (σ X0)
           have i₂ := b1e305 (σ x) X0
           grind)
        | exact superpose b1e305 b1e194516
        | (have j1 := b1e305 (σ x) X0
           grind)
        | exact resolve b1e194516 b1e305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e305 b1e194516
      have b1e197211 : ∀ X0 : G, x = (k x (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e197183 X0
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e197183
        | (have j0 := b1e197183 X0
           grind)
        | exact resolve b1e197183 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e197183
      have b1e456935 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e197211 y
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e197211
        | (have j0 := b1e197211 y
           grind)
        | exact resolve b1e197211 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e197211
      have b1e456936 : x = (k x x) := by
        first
        | (have r₁ := b1e456935
           have r₂ := b1e18
           grind)
        | exact resolve b1e456935 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e456935
      have b1e456948 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e11865 x x
           have i₂ := b1e456936
           grind)
        | exact superpose b1e456936 b1e11865
        | (have j0 := b1e11865 x x
           grind)
        | (have r₁ := b1e11865 x x
           have r₂ := b1e456936
           grind)
        | exact resolve b1e11865 b1e456936
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11865 b1e456936
      have b1e456970 : x = (M.op x x) := by grind
      clear b1e456948
      have b1e457014 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e26 x x x x
           have i₂ := b1e456970
           grind)
        | exact superpose b1e456970 b1e26
        | exact resolve b1e26 b1e456970
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e459061 : ∀ X0 : G, x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b1e456970
           have i₂ := b1e457014 x X0
           grind)
        | (have i₁ := b1e456970
           have i₂ := b1e457014 X0 x
           grind)
        | exact superpose b1e457014 b1e456970
        | exact resolve b1e456970 b1e457014
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e456970
      have b1e459063 : ∀ X0 : G, y = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b1e17
           have i₂ := b1e457014 y X0
           grind)
        | (have i₁ := b1e17
           have i₂ := b1e457014 X0 y
           grind)
        | exact superpose b1e457014 b1e17
        | exact resolve b1e17 b1e457014
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e457014
      have b1e459919 : x = y := by
        first
        | (have i₁ := b1e459061 x
           have i₂ := b1e459063 x
           grind)
        | exact superpose b1e459063 b1e459061
        | exact resolve b1e459061 b1e459063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e459061 b1e459063
      have b1e461028 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e11856
           have i₂ := b1e459919
           grind)
        | exact superpose b1e459919 b1e11856
        | exact resolve b1e11856 b1e459919
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e11856 b1e459919
      have b1e461334 : False := by grind
      exact b1e461334
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
      clear b2e22
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
      have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X0 X1 X3
           have i₂ := b2e10 X0 X1 X2
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b2e52 : x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b2e24
           have i₂ := b2e14 x y
           grind)
        | exact superpose b2e14 b2e24
        | (have j1 := b2e14 x y
           grind)
        | exact resolve b2e24 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e55 : x = (M.op x y) := by
        first
        | (have r₁ := b2e52
           have r₂ := b2e17
           grind)
        | exact resolve b2e52 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e57 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e55
           grind)
        | exact superpose b2e55 b2e19
        | exact resolve b2e19 b2e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e79 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 x y x x
           have i₂ := b2e55
           grind)
        | exact superpose b2e55 b2e34
        | exact resolve b2e34 b2e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e151 : ∀ X0 : G, x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e55
           have i₂ := b2e79 y X0
           grind)
        | (have i₁ := b2e55
           have i₂ := b2e79 X0 y
           grind)
        | exact superpose b2e79 b2e55
        | exact resolve b2e55 b2e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e55 b2e79
      have b2e256 : ∀ X0 : G, x ≠ X0 ∨ x = (k x X0) := by
        intro X0
        first
        | (have i₁ := b2e13 x X0
           have i₂ := b2e151 X0
           grind)
        | exact superpose b2e151 b2e13
        | (have j0 := b2e13 x X0
           grind)
        | (have r₁ := b2e13 x x
           have r₂ := b2e151 x
           grind)
        | exact resolve b2e13 b2e151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e151
      have b2e710 : x = (k x x) := by
        first
        | (have j0 := b2e256 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e256
      have b2e920 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e50 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e12656 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e920 x x
           have i₂ := b2e710
           grind)
        | exact superpose b2e710 b2e920
        | (have j0 := b2e920 x x
           grind)
        | exact resolve b2e920 b2e710
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e710 b2e920
      have b2e12666 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b2e12656
      have b2e12696 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 (σ x) (σ x) x x
           have i₂ := b2e12666
           grind)
        | exact superpose b2e12666 b2e34
        | exact resolve b2e34 b2e12666
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e12932 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b2e18
           have i₂ := b2e12696 (σ y) X0
           grind)
        | (have i₁ := b2e18
           have i₂ := b2e12696 X0 (σ y)
           grind)
        | exact superpose b2e12696 b2e18
        | exact resolve b2e18 b2e12696
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12696
      have b2e13232 : (σ x) = (σ y) := by
        first
        | (have i₁ := b2e12666
           have i₂ := b2e12932 (σ x)
           grind)
        | exact superpose b2e12932 b2e12666
        | exact resolve b2e12666 b2e12932
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e12666 b2e12932
      have b2e13355 : False := by grind
      exact b2e13355
    · have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : y ≠ (M.op x y) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b3e859 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e37 x y
           grind)
        | exact superpose b3e37 b3e16
        | (have j1 := b3e37 x y
           grind)
        | exact resolve b3e16 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37
      have b3e881 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e859
           have r₂ := b3e18
           grind)
        | exact resolve b3e859 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e859
      have b3e884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b3e881
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e881
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e881 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e881
      have b3e885 : y = (M.op x y) := by grind
      clear b3e884
      have b3e886 : False := by grind
      exact b3e886

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4441 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4441 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e18 : y = (M.op y x) := by grind
        have b0e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b0e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e17
          | exact resolve b0e17 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 x X0 y X1
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e11
          | exact resolve b0e11 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e40 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 y X0 x X1
             have i₂ := b0e18
             grind)
          | exact superpose b0e18 b0e11
          | exact resolve b0e11 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 X0 X1 x x
             have i₂ := b0e11 X0 X2 x x
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X0 X1
             have i₂ := b0e15 (σ X0) (σ X1)
             grind)
          | exact superpose b0e15 b0e16
          | (have j1 := b0e15 (σ X0) (σ X1)
             grind)
          | exact resolve b0e16 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e53 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e39 x X2
             have i₂ := b0e39 x X0
             grind)
          | (have i₁ := b0e39 X0 x
             have i₂ := b0e39 X0 (M.op X0 x)
             grind)
          | exact superpose b0e39 b0e39
          | exact resolve b0e39 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e69 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e40 x X2
             have i₂ := b0e40 x X0
             grind)
          | (have i₁ := b0e40 X0 x
             have i₂ := b0e40 X0 (M.op X0 y)
             grind)
          | exact superpose b0e40 b0e40
          | exact resolve b0e40 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e104 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e20
             have i₂ := b0e53 y X0
             grind)
          | (have i₁ := b0e20
             have i₂ := b0e53 X0 y
             grind)
          | exact superpose b0e53 b0e20
          | exact resolve b0e20 b0e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e53
        have b0e129 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b0e14 X0 x
             have i₂ := b0e104 X0
             grind)
          | exact superpose b0e104 b0e14
          | (have j0 := b0e14 X0 x
             grind)
          | (have r₁ := b0e14 X0 x
             have r₂ := b0e104 X0
             grind)
          | exact resolve b0e14 b0e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e133 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b0e129 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e129
        have b0e275 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b0e41 (σ x) X0 (σ y)
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e41
          | exact resolve b0e41 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e278 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b0e41 X0 X1 x
             have i₂ := b0e104 X0
             grind)
          | exact superpose b0e104 b0e41
          | exact resolve b0e41 b0e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e104
        have b0e284 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y (M.op X0 y))) = (M.op X1 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e41 X1 X2 y
             have i₂ := b0e40 X0 X1
             grind)
          | (have i₁ := b0e41 (M.op X0 y) X1 y
             have i₂ := b0e40 X0 X1
             grind)
          | exact superpose b0e40 b0e41
          | exact resolve b0e41 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e333 : (M.op (σ x) (σ y)) = (M.op (σ x) x) := by
          first
          | (have i₁ := b0e275 x
             have i₂ := b0e278 (σ x) x
             grind)
          | exact superpose b0e278 b0e275
          | exact resolve b0e275 b0e278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e275
        have b0e369 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 (M.op y X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e11 X1 y X2 X3
             have i₂ := b0e69 X1 X0
             grind)
          | (have i₁ := b0e11 X1 y X2 X3
             have i₂ := b0e69 X0 X1
             grind)
          | exact superpose b0e69 b0e11
          | exact resolve b0e11 b0e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e381 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e18
             have i₂ := b0e69 x X0
             grind)
          | (have i₁ := b0e18
             have i₂ := b0e69 X0 x
             grind)
          | exact superpose b0e69 b0e18
          | exact resolve b0e18 b0e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e390 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op X1 (M.op y X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e41 X1 X2 y
             have i₂ := b0e69 X1 X0
             grind)
          | (have i₁ := b0e41 X1 X2 y
             have i₂ := b0e69 X0 X1
             grind)
          | exact superpose b0e69 b0e41
          | exact resolve b0e41 b0e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e69
        have b0e396 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e390 X0 X1 x
             have i₂ := b0e278 X1 x
             grind)
          | exact superpose b0e278 b0e390
          | exact resolve b0e390 b0e278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e278 b0e390
        have b0e401 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X1 y) := by
          intro X1 X2 X3
          first
          | (have i₁ := b0e369 x X1 X2 X3
             have i₂ := b0e381 x
             grind)
          | exact superpose b0e381 b0e369
          | exact resolve b0e369 b0e381
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e369
        have b0e402 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b0e396 x X1
             have i₂ := b0e381 x
             grind)
          | exact superpose b0e381 b0e396
          | exact resolve b0e396 b0e381
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e381 b0e396
        have b0e2314 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e48 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48
        have b0e3431 : (σ x) ≠ (M.op (σ x) x) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e333
             grind)
          | exact superpose b0e333 b0e21
          | exact resolve b0e21 b0e333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e21 b0e333
        have b0e3456 : (σ x) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e3431
             have i₂ := b0e402 (σ x)
             grind)
          | exact superpose b0e402 b0e3431
          | exact resolve b0e3431 b0e402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e402 b0e3431
        have b0e6998 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e2314 x
             have i₂ := b0e133 x
             grind)
          | exact superpose b0e133 b0e2314
          | (have j0 := b0e2314 x
             grind)
          | exact resolve b0e2314 b0e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e133 b0e2314
        have b0e7004 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e6998
        have b0e7060 : ∀ X0 : G, (M.op (σ x) (M.op y (M.op X0 y))) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b0e284 X0 (σ x) (σ x)
             have i₂ := b0e7004
             grind)
          | exact superpose b0e7004 b0e284
          | exact resolve b0e284 b0e7004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e284
        have b0e7062 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) y) := by
          intro X0
          first
          | (have i₁ := b0e401 (σ x) (σ x) X0
             have i₂ := b0e7004
             grind)
          | exact superpose b0e7004 b0e401
          | exact resolve b0e401 b0e7004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e401
        have b0e7064 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op y (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b0e7060 X0
             have i₂ := b0e7004
             grind)
          | exact superpose b0e7004 b0e7060
          | exact resolve b0e7060 b0e7004
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e7004 b0e7060
        have b0e7080 : (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b0e7064 x
             have i₂ := b0e7062 (M.op y (M.op x y))
             grind)
          | exact superpose b0e7062 b0e7064
          | exact resolve b0e7064 b0e7062
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e7062 b0e7064
        have b0e7089 : False := by grind
        exact b0e7089
      · have b1e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b1e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e18 : y = (M.op y x) := by grind
        have b1e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
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
        have b1e29 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b1e11 X2 (M.op X0 x) X4 X5
             have i₂ := b1e11 X0 X1 x X2
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b1e11 X0 x X4 X5
             have i₂ := b1e11 X0 x X1 X2
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e11 y X0 x X1
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e11
          | exact resolve b1e11 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X0 X1 x x
             have i₂ := b1e11 X0 X2 x x
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 X0 X4 X1 (M.op x (M.op X0 X1))
             have i₂ := b1e11 (M.op X0 X1) x X2 X3
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e36 x X2
             have i₂ := b1e36 x X0
             grind)
          | (have i₁ := b1e36 X0 x
             have i₂ := b1e36 X0 (M.op X0 y)
             grind)
          | exact superpose b1e36 b1e36
          | exact resolve b1e36 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e80 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e18
             have i₂ := b1e42 x X0
             grind)
          | (have i₁ := b1e18
             have i₂ := b1e42 X0 x
             grind)
          | exact superpose b1e42 b1e18
          | exact resolve b1e18 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e92 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (k (τ X0) X1)
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e103 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X0 y X1 X2
             have i₂ := b1e80 X0
             grind)
          | exact superpose b1e80 b1e11
          | exact resolve b1e11 b1e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e116 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b1e142 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ y) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e31 (σ y) X0 X1 (σ x) X2
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e31
          | exact resolve b1e31 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e174 : ∀ X2 : G, (M.op (σ y) X2) = (M.op (σ y) y) := by
          intro X2
          first
          | (have i₁ := b1e142 x x X2
             have i₂ := b1e103 (σ y) x x
             grind)
          | exact superpose b1e103 b1e142
          | exact resolve b1e142 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e142
        have b1e239 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e37 X0 X1 y
             have i₂ := b1e80 X0
             grind)
          | exact superpose b1e80 b1e37
          | exact resolve b1e37 b1e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e80
        have b1e740 : (σ y) = (M.op (σ y) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e174 (σ x)
             grind)
          | exact superpose b1e174 b1e19
          | exact resolve b1e19 b1e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e897 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e14 X4 (M.op (M.op X0 X2) X3)
             have i₂ := b1e38 X0 X2 X3 X4 X1
             grind)
          | exact superpose b1e38 b1e14
          | (have j0 := b1e14 X4 (M.op (M.op X0 X2) X3)
             grind)
          | exact resolve b1e14 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e919 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X2 X3 X4
          first
          | (have j0 := b1e897 X0 x X2 X3 X4
             grind)
          | (have r₁ := b1e897 X0 x X2 X3 X4
             have r₂ := b1e11 X0 x X2 X3
             grind)
          | exact resolve b1e897 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e897
        have b1e1006 : ∀ X0 X4 : G, (k X4 (M.op X0 y)) = X4 := by
          intro X0 X4
          first
          | (have i₁ := b1e919 X0 x x X4
             have i₂ := b1e103 X0 x x
             grind)
          | exact superpose b1e103 b1e919
          | exact resolve b1e919 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e919
        have b1e1145 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e174 X0
             have i₂ := b1e740
             grind)
          | exact superpose b1e740 b1e174
          | exact resolve b1e174 b1e740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e174 b1e740
        have b1e1355 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 (σ y) x X0 X1 X2
             have i₂ := b1e1145 (M.op x (σ y))
             grind)
          | exact superpose b1e1145 b1e29
          | exact resolve b1e29 b1e1145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e1145
        have b1e1366 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e1355 X0 x x
             have i₂ := b1e103 X0 x x
             grind)
          | exact superpose b1e103 b1e1355
          | exact resolve b1e1355 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1355
        have b1e2217 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e59 X1 X0
             have i₂ := b1e59 X0 X1
             grind)
          | exact superpose b1e59 b1e59
          | (have j0 := b1e59 X1 X0
             have j1 := b1e59 X1 X0
             grind)
          | exact resolve b1e59 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2251 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (σ X1) (σ X0)
             have i₂ := b1e59 X1 X0
             grind)
          | exact superpose b1e59 b1e14
          | (have j0 := b1e14 (σ X1) (σ X0)
             have j1 := b1e59 X1 X0
             grind)
          | (have r₁ := b1e14 (σ X0) (σ X1)
             have r₂ := b1e59 X0 X1
             grind)
          | exact resolve b1e14 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2257 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ X0) X4) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e31 (σ X0) X1 X2 (σ X3) X4
             have i₂ := b1e59 X3 X0
             grind)
          | exact superpose b1e59 b1e31
          | (have j1 := b1e59 X3 X0
             grind)
          | exact resolve b1e31 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e2267 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e59 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2268 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e2251 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2251
        have b1e2273 : ∀ X0 X3 X4 : G, (M.op (σ X0) X4) = (M.op (σ X0) y) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
          intro X0 X3 X4
          first
          | (have i₁ := b1e2257 X0 x x X3 X4
             have i₂ := b1e103 (σ X0) x x
             grind)
          | exact superpose b1e103 b1e2257
          | (have j0 := b1e2257 X0 x x X3 X4
             grind)
          | exact resolve b1e2257 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2257
        have b1e2279 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e2268 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e2268
          | (have j0 := b1e2268 X0 X1
             grind)
          | exact resolve b1e2268 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2268
        have b1e2373 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e1366 (σ x)
             grind)
          | exact superpose b1e1366 b1e17
          | exact resolve b1e17 b1e1366
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1366
        have b1e2680 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e92 X1 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e92
          | exact resolve b1e92 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2682 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e92 X2 (k X0 (τ X1))
             have i₂ := b1e27 X1 X0
             grind)
          | exact superpose b1e27 b1e92
          | exact resolve b1e92 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2856 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e116 X0 (M.op X1 y)
             have i₂ := b1e1006 X1 (σ X0)
             grind)
          | exact superpose b1e1006 b1e116
          | exact resolve b1e116 b1e1006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2876 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 y))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e2856 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e2856
          | exact resolve b1e2856 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2856
        have b1e3072 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 y)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e116 X0 (τ (M.op X1 y))
             have i₂ := b1e2876 (σ X0) X1
             grind)
          | exact superpose b1e2876 b1e116
          | exact resolve b1e116 b1e2876
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2876
        have b1e3075 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 y)))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e3072 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e3072
          | exact resolve b1e3072 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3072
        have b1e4330 : ∀ X0 : G, (σ (M.op X0 y)) ≠ (σ (M.op X0 y)) ∨ (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e2267 (M.op X0 y)
             have i₂ := b1e1006 X0 (M.op X0 y)
             grind)
          | exact superpose b1e1006 b1e2267
          | (have j0 := b1e2267 (M.op X0 y)
             grind)
          | exact resolve b1e2267 b1e1006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1006
        have b1e4344 : ∀ X0 : G, (σ (τ (τ (M.op X0 y)))) ≠ (σ (τ (τ (M.op X0 y)))) ∨ (σ (τ (τ (M.op X0 y)))) = (M.op (σ (τ (τ (M.op X0 y)))) (σ (τ (τ (M.op X0 y))))) := by
          intro X0
          first
          | (have i₁ := b1e2267 (τ (τ (M.op X0 y)))
             have i₂ := b1e3075 (τ (τ (M.op X0 y))) X0
             grind)
          | exact superpose b1e3075 b1e2267
          | (have j0 := b1e2267 (τ (τ (M.op X0 y)))
             grind)
          | exact resolve b1e2267 b1e3075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3075
        have b1e4353 : ∀ X0 : G, (σ (τ (τ (M.op X0 y)))) = (M.op (σ (τ (τ (M.op X0 y)))) (σ (τ (τ (M.op X0 y))))) := by
          intro X0
          first
          | (have j0 := b1e4344 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4344
        have b1e4367 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) := by
          intro X0
          first
          | (have j0 := b1e4330 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4330
        have b1e4372 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) (τ (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e4353 X0
             have i₂ := b1e13 (τ (M.op X0 y))
             grind)
          | exact superpose b1e13 b1e4353
          | exact resolve b1e4353 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4353
        have b1e4936 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e2279 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2279
          | exact resolve b1e2279 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2279
        have b1e5018 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e4936 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e4936
          | (have j0 := b1e4936 X0 X1
             grind)
          | exact resolve b1e4936 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4936
        have b1e5026 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e5018 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e5018
          | (have j0 := b1e5018 X0 X1
             grind)
          | exact resolve b1e5018 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5018
        have b1e5139 : ∀ X0 X1 X2 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e2273 (τ X0) x x
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2273
          | exact resolve b1e2273 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5166 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e59 X2 X0
             have i₂ := b1e2273 X0 X1 (σ X2)
             grind)
          | exact superpose b1e2273 b1e59
          | (have j0 := b1e59 X2 X0
             have j1 := b1e2273 X0 X2 x
             grind)
          | exact resolve b1e59 b1e2273
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e2273
        have b1e5325 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5139 X0 X1 X2
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e5139
          | (have j0 := b1e5139 X0 X1 X2
             grind)
          | exact resolve b1e5139 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5139
        have b1e7510 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e2217 (τ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e2217
          | exact resolve b1e2217 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e7547 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e14 (σ X1) (σ X0)
             have i₂ := b1e2217 X1 X0
             grind)
          | exact superpose b1e2217 b1e14
          | (have j0 := b1e14 (σ X1) (σ X0)
             have j1 := b1e2217 X1 X0
             grind)
          | (have r₁ := b1e14 (σ X0) (σ X1)
             have r₂ := b1e2217 X0 X1
             grind)
          | exact resolve b1e14 b1e2217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2217
        have b1e7582 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e7547 X0 X1
             have j1 := b1e14 (σ X1) (σ X0)
             grind)
          | (have r₁ := b1e7547 X0 X1
             have r₂ := b1e14 (σ X1) (σ X0)
             grind)
          | exact resolve b1e7547 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7547
        have b1e7588 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e7510 X0 X1
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e7510
          | (have j0 := b1e7510 X0 X1
             grind)
          | exact resolve b1e7510 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7510
        have b1e7598 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e7582 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e7582
          | (have j0 := b1e7582 X0 X1
             grind)
          | exact resolve b1e7582 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7582
        have b1e7599 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e7598 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7598
        have b1e7601 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e7588 X0 X1
             have i₂ := b1e26 X0 X1
             grind)
          | exact superpose b1e26 b1e7588
          | (have j0 := b1e7588 X0 X1
             grind)
          | exact resolve b1e7588 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7588
        have b1e7606 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b1e7601 X0 X1
             have j1 := b1e14 X0 (σ X1)
             grind)
          | (have r₁ := b1e7601 X0 X1
             have r₂ := b1e14 X0 (σ X1)
             grind)
          | exact resolve b1e7601 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7601
        have b1e9307 : ∀ X0 : G, (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e239 (σ (M.op X0 y)) (σ (M.op X0 y))
             have i₂ := b1e4367 X0
             grind)
          | exact superpose b1e4367 b1e239
          | exact resolve b1e239 b1e4367
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e9314 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e9307 X0
             have i₂ := b1e4367 X0
             grind)
          | exact superpose b1e4367 b1e9307
          | exact resolve b1e9307 b1e4367
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4367 b1e9307
        have b1e9655 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e7599 (τ X0) (τ X1)
             have i₂ := b1e2680 X1 X0
             grind)
          | exact superpose b1e2680 b1e7599
          | (have j0 := b1e7599 (τ X0) (τ X1)
             grind)
          | exact resolve b1e7599 b1e2680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e9710 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e9655 X0 X1
             have i₂ := b1e13 (k X0 X1)
             grind)
          | exact superpose b1e13 b1e9655
          | (have j0 := b1e9655 X0 X1
             grind)
          | exact resolve b1e9655 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9655
        have b1e9727 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e9710 X0 X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e9710
          | (have j0 := b1e9710 X0 X1
             grind)
          | exact resolve b1e9710 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9710
        have b1e9738 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e9727 X0 X1
             have i₂ := b1e27 X0 (τ X1)
             grind)
          | exact superpose b1e27 b1e9727
          | (have j0 := b1e9727 X0 X1
             grind)
          | exact resolve b1e9727 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9727
        have b1e9740 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e9738 X0 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e9738
          | (have j0 := b1e9738 X0 X1
             grind)
          | exact resolve b1e9738 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9738
        have b1e10779 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (k (τ X1) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e9740 (τ X0) (τ X1)
             have i₂ := b1e2680 X1 X0
             grind)
          | exact superpose b1e2680 b1e9740
          | (have j0 := b1e9740 (τ X0) (τ X1)
             grind)
          | exact resolve b1e9740 b1e2680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e10819 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e10779 X0 X1
             have i₂ := b1e2680 X0 X1
             grind)
          | exact superpose b1e2680 b1e10779
          | (have j0 := b1e10779 X0 X1
             grind)
          | exact resolve b1e10779 b1e2680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2680 b1e10779
        have b1e10826 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e5026 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e5026
          | exact resolve b1e5026 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5026
        have b1e11061 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e7606 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e7606
          | exact resolve b1e7606 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e11120 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e116 X0 (σ X1)
             have i₂ := b1e7606 (σ X0) X1
             grind)
          | exact superpose b1e7606 b1e116
          | (have j1 := b1e7606 (σ X0) X1
             grind)
          | exact resolve b1e116 b1e7606
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116 b1e7606
        have b1e11210 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e11120 X0 X1
             have i₂ := b1e12 X1
             grind)
          | exact superpose b1e12 b1e11120
          | (have j0 := b1e11120 X0 X1
             grind)
          | exact resolve b1e11120 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11120
        have b1e11237 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e11210 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e11210
          | (have j0 := b1e11210 X0 X1
             grind)
          | exact resolve b1e11210 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11210
        have b1e11245 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e11237 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e11237
          | (have j0 := b1e11237 X0 X1
             grind)
          | exact resolve b1e11237 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11237
        have b1e11654 : ∀ X0 X1 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e103 (σ (M.op X0 y)) y x
             have i₂ := b1e9314 X0
             grind)
          | exact superpose b1e9314 b1e103
          | exact resolve b1e103 b1e9314
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9314
        have b1e11950 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 y) = (M.op X1 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5325 X0 (τ X0) X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e5325
          | (have j0 := b1e5325 X1 X1 X2
             grind)
          | exact resolve b1e5325 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5325
        have b1e16216 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e27 X1 X0
             have i₂ := b1e10826 (τ X1) X0
             grind)
          | exact superpose b1e10826 b1e27
          | (have j1 := b1e10826 (τ X1) X0
             grind)
          | exact resolve b1e27 b1e10826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e16271 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e10826 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10826
        have b1e17224 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e7599 X0 X1
             have i₂ := b1e11061 X1 X0
             grind)
          | exact superpose b1e11061 b1e7599
          | (have j0 := b1e7599 X0 X1
             have j1 := b1e11061 X1 X0
             grind)
          | exact resolve b1e7599 b1e11061
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7599
        have b1e17270 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e17224 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17224
        have b1e36884 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 y) = (M.op X1 X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e26 X0 X1
             have i₂ := b1e11950 (τ X0) X1 X2
             grind)
          | exact superpose b1e11950 b1e26
          | (have j1 := b1e11950 X0 X1 X2
             grind)
          | exact resolve b1e26 b1e11950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37076 : ∀ X0 X1 : G, x ≠ (M.op x X0) ∨ (k X1 x) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e20
             have i₂ := b1e11950 X1 x X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e11950 X0 x y
             grind)
          | exact superpose b1e11950 b1e20
          | (have j1 := b1e11950 X1 x x
             grind)
          | exact resolve b1e20 b1e11950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11950
        have b1e41595 : ∀ X0 : G, (M.op (τ (M.op X0 y)) (τ (M.op X0 y))) = (M.op (τ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e239 (τ (M.op X0 y)) (τ (M.op X0 y))
             have i₂ := b1e4372 X0
             grind)
          | exact superpose b1e4372 b1e239
          | exact resolve b1e239 b1e4372
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41604 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e41595 X0
             have i₂ := b1e4372 X0
             grind)
          | exact superpose b1e4372 b1e41595
          | exact resolve b1e41595 b1e4372
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4372 b1e41595
        have b1e45258 : ∀ X0 X1 : G, (τ (M.op X0 y)) = (M.op (τ (M.op X0 y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e103 (τ (M.op X0 y)) y x
             have i₂ := b1e41604 X0
             grind)
          | exact superpose b1e41604 b1e103
          | exact resolve b1e103 b1e41604
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41604
        have b1e73347 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e10819 X0 X1
             have i₂ := b1e11061 X1 X0
             grind)
          | exact superpose b1e11061 b1e10819
          | (have j0 := b1e10819 X0 X1
             have j1 := b1e11061 X1 X0
             grind)
          | exact resolve b1e10819 b1e11061
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10819 b1e11061
        have b1e73537 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e73347 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73347
        have b1e74534 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e2267 X0
             have i₂ := b1e17270 X0 X0
             grind)
          | exact superpose b1e17270 b1e2267
          | (have j0 := b1e2267 X0
             have j1 := b1e17270 X0 X0
             grind)
          | (have r₁ := b1e2267 X0
             have r₂ := b1e17270 X0 X0
             grind)
          | exact resolve b1e2267 b1e17270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2267 b1e17270
        have b1e74719 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have j0 := b1e74534 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74534
        have b1e78461 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e73537 (σ X1) (σ X0)
             have i₂ := b1e16 X0 X1
             grind)
          | exact superpose b1e16 b1e73537
          | exact resolve b1e73537 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73537
        have b1e78613 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e78461 X0 X1
             have i₂ := b1e12 (k X0 X1)
             grind)
          | exact superpose b1e12 b1e78461
          | (have j0 := b1e78461 X0 X1
             grind)
          | exact resolve b1e78461 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78461
        have b1e78622 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e78613 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e78613
          | (have j0 := b1e78613 X0 X1
             grind)
          | exact resolve b1e78613 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78613
        have b1e83014 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) y) := by
          intro X0 X1
          first
          | (have j0 := b1e5166 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5166
        have b1e83015 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) y) := by
          intro X0 X1
          first
          | (have j0 := b1e83014 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83014
        have b1e105730 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (M.op (σ X0) y) ∨ (k X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e103 (σ X0) (σ X1) X2
             have i₂ := b1e11245 X1 X0
             grind)
          | exact superpose b1e11245 b1e103
          | (have j1 := b1e11245 X1 X0
             grind)
          | exact resolve b1e103 b1e11245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11245
        have b1e128967 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ X0) y) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e103 (σ X0) (σ X0) X1
             have i₂ := b1e74719 X0
             grind)
          | exact superpose b1e74719 b1e103
          | (have j1 := b1e74719 X0
             grind)
          | exact resolve b1e103 b1e74719
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e133999 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (M.op (σ X0) y) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e103 (σ X0) (σ X1) X2
             have i₂ := b1e78622 X0 X1
             grind)
          | exact superpose b1e78622 b1e103
          | (have j1 := b1e78622 X0 X1
             grind)
          | exact resolve b1e103 b1e78622
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78622
        have b1e163980 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e16216 X0 (σ X0)
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e16216
          | exact resolve b1e16216 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16216
        have b1e164126 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e163980 X0 X1
             have i₂ := b1e16 X1 X0
             grind)
          | exact superpose b1e16 b1e163980
          | (have j0 := b1e163980 X0 X1
             grind)
          | exact resolve b1e163980 b1e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e163980
        have b1e197393 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (k X0 X0) = (M.op X0 X0) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e74719 X0
             have i₂ := b1e128967 X0 (σ X0)
             grind)
          | exact superpose b1e128967 b1e74719
          | (have j0 := b1e74719 X0
             have j1 := b1e128967 X0 x
             grind)
          | exact resolve b1e74719 b1e128967
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74719 b1e128967
        have b1e197704 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have j0 := b1e197393 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e197393
        have b1e198257 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e45258 (σ X0) X1
             have i₂ := b1e197704 X0
             grind)
          | exact superpose b1e197704 b1e45258
          | (have j1 := b1e197704 X0
             grind)
          | exact resolve b1e45258 b1e197704
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45258 b1e197704
        have b1e198476 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e198257 X0 X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e198257
          | (have j0 := b1e198257 X0 X1
             grind)
          | exact resolve b1e198257 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e198257
        have b1e199417 : ∀ X1 : G, x ≠ x ∨ (k X1 x) = (M.op X1 x) ∨ (k x x) = (M.op x x) := by
          intro X1
          first
          | (have i₁ := b1e37076 x X1
             have i₂ := b1e198476 x x
             grind)
          | exact superpose b1e198476 b1e37076
          | (have j0 := b1e37076 x X1
             have j1 := b1e198476 x X1
             grind)
          | (have r₁ := b1e37076 X1 X1
             have r₂ := b1e198476 x X1
             grind)
          | exact resolve b1e37076 b1e198476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e198476
        have b1e199533 : ∀ X1 : G, (k X1 x) = (M.op X1 x) ∨ (k x x) = (M.op x x) := by
          intro X1
          first
          | (have j0 := b1e199417 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e199417
        have b1e210248 : (M.op x x) ≠ (M.op x x) ∨ (k x x) = (M.op x x) := by
          first
          | (have j0 := b1e199533 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e199533
        have b1e210249 : (k x x) = (M.op x x) := by grind
        clear b1e210248
        have b1e211488 : ∀ X0 : G, (M.op (σ x) y) = (M.op (σ (M.op x x)) X0) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b1e105730 x x x
             have i₂ := b1e210249
             grind)
          | exact superpose b1e210249 b1e105730
          | exact resolve b1e105730 b1e210249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105730
        have b1e246444 : ∀ X0 X1 X2 : G, (M.op (σ X0) y) = (M.op (σ (M.op X0 X1)) X2) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e133999 X0 X1 X2
             have i₂ := b1e164126 X1 X0
             grind)
          | exact superpose b1e164126 b1e133999
          | (have j0 := b1e133999 X0 X1 X2
             have j1 := b1e164126 X1 X0
             grind)
          | exact resolve b1e133999 b1e164126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e133999 b1e164126
        have b1e246685 : ∀ X0 X1 X2 : G, (M.op (σ X0) y) = (M.op (σ (M.op X0 X1)) X2) ∨ (k X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b1e246444 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e246444
        have b1e272045 : ∀ X0 X1 X2 : G, (M.op (σ X0) y) = (M.op (σ (M.op X0 y)) X2) ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e246685 X0 (M.op X1 X0) X2
             have i₂ := b1e239 X0 X1
             grind)
          | exact superpose b1e239 b1e246685
          | (have j0 := b1e246685 X0 y X2
             grind)
          | exact resolve b1e246685 b1e239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e239 b1e246685
        have b1e272351 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (σ (M.op X0 y)) = (M.op (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e272045 X0 X1 x
             have i₂ := b1e11654 X0 x
             grind)
          | exact superpose b1e11654 b1e272045
          | (have j0 := b1e272045 X0 X1 x
             grind)
          | exact resolve b1e272045 b1e11654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e272045
        have b1e297307 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e83015 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e83015
          | exact resolve b1e83015 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83015
        have b1e297418 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e297307 X0 X1
             have i₂ := b1e27 X0 X1
             grind)
          | exact superpose b1e27 b1e297307
          | (have j0 := b1e297307 X0 X1
             grind)
          | exact resolve b1e297307 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e297307
        have b1e297430 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e297418 X0 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e297418
          | (have j0 := b1e297418 X1 X1
             grind)
          | exact resolve b1e297418 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e297418
        have b1e297927 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e26 X0 X1
             have i₂ := b1e297430 (τ X0) X1
             grind)
          | exact superpose b1e297430 b1e26
          | (have j1 := b1e297430 X0 X1
             grind)
          | exact resolve b1e26 b1e297430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e297430
        have b1e322909 : ∀ X0 X1 X2 : G, (M.op X0 y) ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X2 (σ X0)) = (σ (M.op (τ X2) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16271 X0 X1
             have i₂ := b1e36884 X2 X0 X1
             grind)
          | (have i₁ := b1e16271 X1 y
             have i₂ := b1e36884 X0 X1 X2
             grind)
          | exact superpose b1e36884 b1e16271
          | (have j0 := b1e16271 X0 y
             have j1 := b1e36884 X2 X0 X2
             grind)
          | exact resolve b1e16271 b1e36884
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16271 b1e36884
        have b1e322939 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X2 (σ X0)) = (σ (M.op (τ X2) X0)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e322909 X0 X1 X2
             have j1 := b1e297927 X2 X0
             grind)
          | (have r₁ := b1e322909 X1 X1 X2
             have r₂ := b1e297927 X0 X1
             grind)
          | exact resolve b1e322909 b1e297927
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e297927 b1e322909
        have b1e323200 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op (τ X0) X1)
             have i₂ := b1e322939 X1 X2 X0
             grind)
          | exact superpose b1e322939 b1e12
          | (have j1 := b1e322939 X1 X2 X2
             grind)
          | exact resolve b1e12 b1e322939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e322939
        have b1e323221 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e323200 X0 X1 X2
             have i₂ := b1e92 X0 X1
             grind)
          | exact superpose b1e92 b1e323200
          | (have j0 := b1e323200 X0 X1 X2
             grind)
          | exact resolve b1e323200 b1e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92 b1e323200
        have b1e323285 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X2) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e323221 (σ X0) X1 X2
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e323221
          | (have j0 := b1e323221 X0 X1 X2
             grind)
          | exact resolve b1e323221 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e323221
        have b1e324190 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e210249
             have i₂ := b1e323285 X0 x x
             grind)
          | exact superpose b1e323285 b1e210249
          | (have j1 := b1e323285 X0 x x
             grind)
          | exact resolve b1e210249 b1e323285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e210249 b1e323285
        have b1e324204 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e324190 X0
             have j1 := b1e37076 X0 X0
             grind)
          | (have r₁ := b1e324190 X0
             have r₂ := b1e37076 x x
             grind)
          | exact resolve b1e324190 b1e37076
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37076 b1e324190
        have b1e324510 : ∀ X0 X1 : G, (k (τ X1) (k X0 (τ x))) = (τ (k X1 (M.op (σ X0) x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2682 X0 x X1
             have i₂ := b1e324204 (σ X0)
             grind)
          | exact superpose b1e324204 b1e2682
          | exact resolve b1e2682 b1e324204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2682
        have b1e348595 : ∀ X0 : G, (τ x) = (k (τ x) (k X0 (τ x))) ∨ (σ (M.op x y)) = (M.op (σ x) y) := by
          intro X0
          first
          | (have i₁ := b1e324510 X0 x
             have i₂ := b1e272351 x (σ X0)
             grind)
          | exact superpose b1e272351 b1e324510
          | (have j1 := b1e272351 x x
             grind)
          | exact resolve b1e324510 b1e272351
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e272351 b1e324510
        have b1e348702 : ∀ X0 : G, (τ x) = (k (τ x) (k X0 (τ x))) := by
          intro X0
          first
          | (have j0 := b1e348595 X0
             grind)
          | (have r₁ := b1e348595 X0
             have r₂ := b1e2373
             grind)
          | exact resolve b1e348595 b1e2373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e348595
        have b1e348973 : ∀ X0 : G, (σ (τ x)) = (k x (σ (k X0 (τ x)))) := by
          intro X0
          first
          | (have i₁ := b1e26 x (k X0 (τ x))
             have i₂ := b1e348702 X0
             grind)
          | exact superpose b1e348702 b1e26
          | exact resolve b1e26 b1e348702
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e348702
        have b1e349016 : ∀ X0 : G, (σ (τ x)) = (k x (k (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e348973 X0
             have i₂ := b1e27 x X0
             grind)
          | exact superpose b1e27 b1e348973
          | exact resolve b1e348973 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e348973
        have b1e349067 : ∀ X0 : G, (σ (τ x)) = (k x (M.op (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e349016 X0
             have i₂ := b1e324204 (σ X0)
             grind)
          | exact superpose b1e324204 b1e349016
          | exact resolve b1e349016 b1e324204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e349016
        have b1e349092 : ∀ X0 : G, x = (k x (M.op (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e349067 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e349067
          | exact resolve b1e349067 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e349067
        have b1e349148 : ∀ X0 : G, x = (k x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e349092 (τ X0)
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e349092
          | exact resolve b1e349092 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e349092
        have b1e349591 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b1e9740 x (M.op X0 x)
             have i₂ := b1e349148 X0
             grind)
          | exact superpose b1e349148 b1e9740
          | (have j0 := b1e9740 x (M.op X0 x)
             grind)
          | (have r₁ := b1e9740 x (M.op X0 x)
             have r₂ := b1e349148 X0
             grind)
          | exact resolve b1e9740 b1e349148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9740 b1e349148
        have b1e349651 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) x) := by
          intro X0
          first
          | (have j0 := b1e349591 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e349591
        have b1e349698 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b1e349651 X0
             have i₂ := b1e324204 (M.op X0 x)
             grind)
          | exact superpose b1e324204 b1e349651
          | exact resolve b1e349651 b1e324204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e324204 b1e349651
        have b1e349745 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e349698 X0
             have i₂ := b1e103 X0 x x
             grind)
          | exact superpose b1e103 b1e349698
          | exact resolve b1e349698 b1e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e103 b1e349698
        have b1e350890 : ∀ X0 : G, (M.op (σ x) y) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b1e211488 X0
             have i₂ := b1e349745 x
             grind)
          | exact superpose b1e349745 b1e211488
          | exact resolve b1e211488 b1e349745
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e211488 b1e349745
        have b1e350935 : ∀ X0 : G, (M.op (σ x) y) = (M.op (σ (M.op x y)) X0) := by
          intro X0
          first
          | (have j0 := b1e350890 X0
             grind)
          | (have r₁ := b1e350890 X0
             have r₂ := b1e20
             grind)
          | exact resolve b1e350890 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e350890
        have b1e350984 : (σ (M.op x y)) = (M.op (σ x) y) := by
          first
          | (have i₁ := b1e350935 x
             have i₂ := b1e11654 x x
             grind)
          | exact superpose b1e11654 b1e350935
          | exact resolve b1e350935 b1e11654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11654 b1e350935
        have b1e350999 : False := by grind
        exact b1e350999
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b2e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e17
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e17
          | exact resolve b2e17 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e23 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b2e14 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e14
          | (have j0 := b2e14 y x
             grind)
          | (have r₁ := b2e14 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e14 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e24 : y = (k y x) := by grind
        clear b2e23
        have b2e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e1993 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e43 y x
             grind)
          | exact superpose b2e43 b2e21
          | (have j1 := b2e43 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e43 y x
             grind)
          | exact resolve b2e21 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21 b2e43
        have b2e2014 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
        clear b2e1993
        have b2e2028 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e2014
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e2014
          | exact resolve b2e2014 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e2014
        have b2e2061 : False := by grind
        exact b2e2061
      · have b3e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b3e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e18 : y = (M.op y x) := by grind
        have b3e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b3e29 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e11 y X0 x X1
             have i₂ := b3e18
             grind)
          | exact superpose b3e18 b3e11
          | exact resolve b3e11 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e11 X0 X1 x x
             have i₂ := b3e11 X0 X2 x x
             grind)
          | exact superpose b3e11 b3e11
          | exact resolve b3e11 b3e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b3e29 x X2
             have i₂ := b3e29 x X0
             grind)
          | (have i₁ := b3e29 X0 x
             have i₂ := b3e29 X0 (M.op X0 y)
             grind)
          | exact superpose b3e29 b3e29
          | exact resolve b3e29 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e75 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e18
             have i₂ := b3e37 x X0
             grind)
          | (have i₁ := b3e18
             have i₂ := b3e37 X0 x
             grind)
          | exact superpose b3e37 b3e18
          | exact resolve b3e18 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e98 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e11 X0 y X1 X2
             have i₂ := b3e75 X0
             grind)
          | exact superpose b3e75 b3e11
          | exact resolve b3e11 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e99 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e14 X0 y
             have i₂ := b3e75 X0
             grind)
          | exact superpose b3e75 b3e14
          | (have j0 := b3e14 X0 y
             grind)
          | (have r₁ := b3e14 X0 y
             have r₂ := b3e75 X0
             grind)
          | exact resolve b3e14 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e102 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e99 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e222 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X0 X1 y
             have i₂ := b3e75 X0
             grind)
          | exact superpose b3e75 b3e32
          | exact resolve b3e32 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e75
        have b3e2017 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e54 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e3681 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e2017 y
             have i₂ := b3e102 y
             grind)
          | exact superpose b3e102 b3e2017
          | (have j0 := b3e2017 y
             grind)
          | exact resolve b3e2017 b3e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102 b3e2017
        have b3e3686 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b3e3681
        have b3e3735 : (M.op (σ y) (σ y)) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e222 (σ y) (σ y)
             have i₂ := b3e3686
             grind)
          | exact superpose b3e3686 b3e222
          | exact resolve b3e222 b3e3686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e222
        have b3e3741 : (σ y) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e3735
             have i₂ := b3e3686
             grind)
          | exact superpose b3e3686 b3e3735
          | exact resolve b3e3735 b3e3686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3686 b3e3735
        have b3e3841 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e98 (σ y) y x
             have i₂ := b3e3741
             grind)
          | exact superpose b3e3741 b3e98
          | exact resolve b3e98 b3e3741
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98 b3e3741
        have b3e3991 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e3841 (σ x)
             grind)
          | exact superpose b3e3841 b3e19
          | (have r₁ := b3e19
             have r₂ := b3e3841 (σ x)
             grind)
          | exact resolve b3e19 b3e3841
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3841
        have b3e4050 : False := by grind
        exact b3e4050
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b4e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b4e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b4e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b4e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b4e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b4e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b4e18 : y ≠ (M.op y x) := by grind
        have b4e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b4e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b4e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 X1 (τ X0)
             have i₂ := b4e13 X0
             grind)
          | exact superpose b4e13 b4e16
          | exact resolve b4e16 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e32 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b4e11 X0 x X4 X5
             have i₂ := b4e11 X0 x X1 X2
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e37 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b4e11 x X0 y X1
             have i₂ := b4e20
             grind)
          | exact superpose b4e20 b4e11
          | exact resolve b4e11 b4e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e11 X0 X1 x x
             have i₂ := b4e11 X0 X2 x x
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b4e11 X0 X4 X1 (M.op x (M.op X0 X1))
             have i₂ := b4e11 (M.op X0 X1) x X2 X3
             grind)
          | exact superpose b4e11 b4e11
          | exact resolve b4e11 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b4e16 X0 X1
             have i₂ := b4e15 (σ X0) (σ X1)
             grind)
          | exact superpose b4e15 b4e16
          | (have j1 := b4e15 (σ X0) (σ X1)
             grind)
          | exact resolve b4e16 b4e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e57 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b4e37 x X2
             have i₂ := b4e37 x X0
             grind)
          | (have i₁ := b4e37 X0 x
             have i₂ := b4e37 X0 (M.op X0 x)
             grind)
          | exact superpose b4e37 b4e37
          | exact resolve b4e37 b4e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e37
        have b4e91 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b4e20
             have i₂ := b4e57 y X0
             grind)
          | (have i₁ := b4e20
             have i₂ := b4e57 X0 y
             grind)
          | exact superpose b4e57 b4e20
          | exact resolve b4e20 b4e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e57
        have b4e114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e11 X0 x X1 X2
             have i₂ := b4e91 X0
             grind)
          | exact superpose b4e91 b4e11
          | exact resolve b4e11 b4e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b4e127 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b4e12 (k X0 (τ X1))
             have i₂ := b4e28 X1 X0
             grind)
          | exact superpose b4e28 b4e12
          | exact resolve b4e12 b4e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e28
        have b4e153 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ y) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b4e32 (σ y) X0 X1 (σ x) X2
             have i₂ := b4e19
             grind)
          | exact superpose b4e19 b4e32
          | exact resolve b4e32 b4e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e32
        have b4e185 : ∀ X2 : G, (M.op (σ y) X2) = (M.op (σ y) x) := by
          intro X2
          first
          | (have i₁ := b4e153 x x X2
             have i₂ := b4e114 (σ y) x x
             grind)
          | exact superpose b4e114 b4e153
          | exact resolve b4e153 b4e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e153
        have b4e250 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b4e38 X0 X1 x
             have i₂ := b4e91 X0
             grind)
          | exact superpose b4e91 b4e38
          | exact resolve b4e38 b4e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e38 b4e91
        have b4e752 : (σ y) = (M.op (σ y) x) := by
          first
          | (have i₁ := b4e19
             have i₂ := b4e185 (σ x)
             grind)
          | exact superpose b4e185 b4e19
          | exact resolve b4e19 b4e185
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e185
        have b4e909 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b4e14 X4 (M.op (M.op X0 X2) X3)
             have i₂ := b4e39 X0 X2 X3 X4 X1
             grind)
          | exact superpose b4e39 b4e14
          | (have j0 := b4e14 X4 (M.op (M.op X0 X2) X3)
             grind)
          | exact resolve b4e14 b4e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e39
        have b4e931 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
          intro X0 X2 X3 X4
          first
          | (have j0 := b4e909 X0 x X2 X3 X4
             grind)
          | (have r₁ := b4e909 X0 x X2 X3 X4
             have r₂ := b4e11 X0 x X2 X3
             grind)
          | exact resolve b4e909 b4e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e909
        have b4e1018 : ∀ X0 X4 : G, (k X4 (M.op X0 x)) = X4 := by
          intro X0 X4
          first
          | (have i₁ := b4e931 X0 x x X4
             have i₂ := b4e114 X0 x x
             grind)
          | exact superpose b4e114 b4e931
          | exact resolve b4e931 b4e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e114 b4e931
        have b4e1157 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b4e1018 (σ y) X0
             have i₂ := b4e752
             grind)
          | exact superpose b4e752 b4e1018
          | exact resolve b4e1018 b4e752
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e752 b4e1018
        have b4e1340 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b4e16 X0 y
             have i₂ := b4e1157 (σ X0)
             grind)
          | exact superpose b4e1157 b4e16
          | exact resolve b4e16 b4e1157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1157
        have b4e2230 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b4e50 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e50
        have b4e2297 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b4e12 (k X0 y)
             have i₂ := b4e1340 X0
             grind)
          | exact superpose b4e1340 b4e12
          | exact resolve b4e12 b4e1340
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e1340
        have b4e2306 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b4e2297 X0
             have i₂ := b4e12 X0
             grind)
          | exact superpose b4e12 b4e2297
          | exact resolve b4e2297 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2297
        have b4e2659 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b4e127 X0 y
             have i₂ := b4e2306 (σ X0)
             grind)
          | exact superpose b4e2306 b4e127
          | exact resolve b4e127 b4e2306
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e127 b4e2306
        have b4e2667 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b4e2659 X0
             have i₂ := b4e12 X0
             grind)
          | exact superpose b4e12 b4e2659
          | exact resolve b4e2659 b4e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2659
        have b4e4319 : (σ (τ y)) ≠ (σ (τ y)) ∨ (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by
          first
          | (have i₁ := b4e2230 (τ y)
             have i₂ := b4e2667 (τ y)
             grind)
          | exact superpose b4e2667 b4e2230
          | (have j0 := b4e2230 (τ y)
             grind)
          | exact resolve b4e2230 b4e2667
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e2230 b4e2667
        have b4e4329 : (σ (τ y)) = (M.op (σ (τ y)) (σ (τ y))) := by grind
        clear b4e4319
        have b4e4348 : y = (M.op y y) := by
          first
          | (have i₁ := b4e4329
             have i₂ := b4e13 y
             grind)
          | exact superpose b4e13 b4e4329
          | exact resolve b4e4329 b4e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e4329
        have b4e4374 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b4e250 y y
             have i₂ := b4e4348
             grind)
          | exact superpose b4e4348 b4e250
          | exact resolve b4e250 b4e4348
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e250
        have b4e4376 : y = (M.op y x) := by
          first
          | (have i₁ := b4e4374
             have i₂ := b4e4348
             grind)
          | exact superpose b4e4348 b4e4374
          | exact resolve b4e4374 b4e4348
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e4348 b4e4374
        have b4e4387 : False := by grind
        exact b4e4387
      · have b5e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b5e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b5e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b5e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b5e18 : y ≠ (M.op y x) := by grind
        have b5e19 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b5e20 : x ≠ (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b5e21 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b5e14 (σ x) (σ y)
             have i₂ := b5e19
             grind)
          | exact superpose b5e19 b5e14
          | (have j0 := b5e14 (σ x) (σ y)
             grind)
          | (have r₁ := b5e14 (σ x) (σ y)
             have r₂ := b5e19
             grind)
          | exact resolve b5e14 b5e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b5e22 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b5e21
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
        have b5e24 : (k x y) = (τ (σ x)) := by
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
        have b5e25 : x = (k x y) := by
          first
          | (have i₁ := b5e24
             have i₂ := b5e12 x
             grind)
          | exact superpose b5e12 b5e24
          | exact resolve b5e24 b5e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e24
        have b5e61 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b5e25
             have i₂ := b5e15 x y
             grind)
          | exact superpose b5e15 b5e25
          | (have j1 := b5e15 y x
             grind)
          | exact resolve b5e25 b5e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e25
        have b5e64 : y = (M.op y x) := by
          first
          | (have r₁ := b5e61
             have r₂ := b5e20
             grind)
          | exact resolve b5e61 b5e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e61
        have b5e66 : False := by grind
        exact b5e66
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b6e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b6e20 : x = (M.op x y) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e17
          | exact resolve b6e17 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e22 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b6e14 y x
             have i₂ := b6e20
             grind)
          | exact superpose b6e20 b6e14
          | (have j0 := b6e14 y x
             grind)
          | (have r₁ := b6e14 y x
             have r₂ := b6e20
             grind)
          | exact resolve b6e14 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e23 : y = (k y x) := by grind
        clear b6e22
        have b6e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e15 (σ X0) (σ X1)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 (σ X0) (σ X1)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1998 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e54 y x
             grind)
          | exact superpose b6e54 b6e21
          | (have j1 := b6e54 y x
             grind)
          | (have r₁ := b6e21
             have r₂ := b6e54 y x
             grind)
          | exact resolve b6e21 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e21 b6e54
        have b6e2020 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
        clear b6e1998
        have b6e2034 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e2020
             have i₂ := b6e23
             grind)
          | exact superpose b6e23 b6e2020
          | exact resolve b6e2020 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e2020
        have b6e2059 : False := by grind
        exact b6e2059
      · have b7e15 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b7e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b7e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b7e18 : y ≠ (M.op y x) := by grind
        have b7e19 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b7e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b7e16 X0 X1
             have i₂ := b7e15 (σ X0) (σ X1)
             grind)
          | exact superpose b7e15 b7e16
          | (have j1 := b7e15 (σ X0) (σ X1)
             grind)
          | exact resolve b7e16 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e793 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e46 x y
             grind)
          | exact superpose b7e46 b7e17
          | (have j1 := b7e46 x y
             grind)
          | exact resolve b7e17 b7e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e46
        have b7e843 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b7e793
             have r₂ := b7e19
             grind)
          | exact resolve b7e793 b7e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e793
        have b7e848 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b7e843
             have i₂ := b7e15 x y
             grind)
          | exact superpose b7e15 b7e843
          | (have j1 := b7e15 x y
             grind)
          | exact resolve b7e843 b7e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e843
        have b7e849 : y = (M.op y x) := by grind
        clear b7e848
        have b7e850 : False := by grind
        exact b7e850
