import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation138`: `x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pxy_Equation138 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law138 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law138.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ y) ≠ (σ y) := by
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
      have b0e23 : False := by grind
      exact b0e23
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e35 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) (σ x)
             grind)
          | (have r₁ := b1e15 (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : y ≠ y ∨ (k x y) = (M.op y x) := by
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
        have b1e39 : (k x y) = (M.op y x) := by grind
        clear b1e37
        have b1e40 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b1e35
        have b1e41 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e40
          | exact resolve b1e40 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e48 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e49 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e48
             have r₂ := b1e21
             grind)
          | exact resolve b1e48 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e50 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e50
          | exact resolve b1e50 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e50
        have b1e54 : (M.op y x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e13
          | exact resolve b1e13 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e55 : x = (M.op y x) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e54
          | exact resolve b1e54 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e64 : x ≠ x ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e15
          | (have j0 := b1e15 y x
             grind)
          | (have r₁ := b1e15 y x
             have r₂ := b1e55
             grind)
          | exact resolve b1e15 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e66 : (M.op x y) = (k y x) := by grind
        clear b1e64
        have b1e68 : y = (k y x) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e66
          | exact resolve b1e66 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e90 : (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e21
          | exact resolve b1e21 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e99 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e90
             have i₂ := b1e68
             grind)
          | exact superpose b1e68 b1e90
          | exact resolve b1e90 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e90
        have b1e100 : False := by grind
        exact b1e100
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X1)) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op (M.op X3 (M.op X2 X1)) X0) X1 X2
             have i₂ := b2e12 X0 (M.op X2 X1) X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e24 (M.op (M.op X1 y) X0)
             have i₂ := b2e12 X0 y X1
             grind)
          | exact superpose b2e12 b2e24
          | exact resolve b2e24 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op y X0) y
             have i₂ := b2e24 X0
             grind)
          | exact superpose b2e24 b2e12
          | exact resolve b2e12 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e40 : y ≠ y ∨ (k x y) = (M.op y x) := by
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
        have b2e42 : (k x y) = (M.op y x) := by grind
        clear b2e40
        have b2e45 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : y = (k y x) ∨ x = (M.op y x) := by grind
        clear b2e45
        have b2e59 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X1 X0) (M.op y X1)
             have i₂ := b2e28 X1 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e79 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e29 X0 X1
             grind)
          | exact superpose b2e29 b2e13
          | exact resolve b2e13 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e165 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e79 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e79
          | exact resolve b2e79 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e271 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (σ X1) (σ X0)
             have i₂ := b2e63 X0 X1
             grind)
          | exact superpose b2e63 b2e12
          | (have j1 := b2e63 X0 X1
             grind)
          | exact resolve b2e12 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e281 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e63 y x
             grind)
          | exact superpose b2e63 b2e21
          | (have j1 := b2e63 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e63 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e63 x y
             grind)
          | exact resolve b2e21 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e283 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X1) (σ X0)
             have i₂ := b2e63 X0 X1
             grind)
          | exact superpose b2e63 b2e15
          | (have j0 := b2e15 (σ X1) (σ X0)
             have j1 := b2e63 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X1) (σ X0)
             have r₂ := b2e63 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e63 X0 X1
             grind)
          | exact resolve b2e15 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e284 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X0) (σ X1)
             have i₂ := b2e63 X0 X1
             grind)
          | exact superpose b2e63 b2e16
          | (have j0 := b2e16 (σ X0) (σ X1)
             have j1 := b2e63 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X0) (σ X1)
             have r₂ := b2e63 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e63 X0 X1
             grind)
          | exact resolve b2e16 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e293 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e295 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e284 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e284
        have b2e296 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e295 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e295
        have b2e297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e283 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e283
        have b2e298 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e281
        have b2e302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e296 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e296
          | (have j0 := b2e296 X0 X1
             grind)
          | exact resolve b2e296 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e296
        have b2e303 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e297 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e297
          | (have j0 := b2e297 X0 X1
             grind)
          | exact resolve b2e297 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e297
        have b2e304 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e298
             have r₂ := b2e22
             grind)
          | exact resolve b2e298 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e298
        have b2e312 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e304
             grind)
          | exact superpose b2e304 b2e22
          | exact resolve b2e22 b2e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e322 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ (k y x))) := by
          intro X0
          first
          | (have i₁ := b2e59 (σ y) X0 (σ x)
             have i₂ := b2e304
             grind)
          | exact superpose b2e304 b2e59
          | exact resolve b2e59 b2e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e353 : (σ x) ≠ (σ y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e312
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e312
          | exact resolve b2e312 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e312
        have b2e804 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b2e322 X0
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e322
          | exact resolve b2e322 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e322
        have b2e947 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e293 (τ X0) (τ X1)
             have i₂ := b2e165 X1 X0
             grind)
          | exact superpose b2e165 b2e293
          | (have j0 := b2e293 (τ X0) (τ X1)
             grind)
          | exact resolve b2e293 b2e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e165 b2e293
        have b2e958 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e947 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e947
          | (have j0 := b2e947 X0 X1
             grind)
          | exact resolve b2e947 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e947
        have b2e962 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e958 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e958
          | (have j0 := b2e958 X0 X1
             grind)
          | exact resolve b2e958 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e958
        have b2e964 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e962 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e962
          | (have j0 := b2e962 X0 X1
             grind)
          | exact resolve b2e962 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e962
        have b2e965 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e964 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e964
          | (have j0 := b2e964 X0 X1
             grind)
          | exact resolve b2e964 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e964
        have b2e966 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e965 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e965
          | (have j0 := b2e965 X0 X1
             grind)
          | exact resolve b2e965 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e965
        have b2e967 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e966 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e966
          | (have j0 := b2e966 X0 X1
             grind)
          | exact resolve b2e966 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e966
        have b2e973 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = (σ (k X1 (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e302 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e302
          | (have j0 := b2e302 X1 (τ X0)
             grind)
          | exact resolve b2e302 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1007 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = (σ (k X1 (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e973 X0 X1
             have i₂ := b2e30 X0 X1
             grind)
          | exact superpose b2e30 b2e973
          | (have j0 := b2e973 X0 X1
             grind)
          | exact resolve b2e973 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e973
        have b2e1010 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (k (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1007 X0 X1
             have i₂ := b2e30 X0 X1
             grind)
          | exact superpose b2e30 b2e1007
          | (have j0 := b2e1007 X0 X1
             grind)
          | exact resolve b2e1007 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1007
        have b2e1279 : ∀ X0 : G, (M.op (σ y) (M.op (σ (M.op y x)) X0)) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e271 x y X0
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e271
          | (have j0 := b2e271 x y x
             grind)
          | exact resolve b2e271 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e271
        have b2e1326 : ∀ X0 : G, (M.op (σ y) (M.op (σ (M.op y x)) X0)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e1279 X0
             grind)
          | (have r₁ := b2e1279 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e1279 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1279
        have b2e1331 : ∀ X0 : G, (M.op (σ y) (M.op (σ (M.op y x)) X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e1326 X0
             grind)
          | (have r₁ := b2e1326 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e1326 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1326
        have b2e1342 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ (M.op y x))) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e1331 (M.op (M.op X1 (σ (M.op y x))) X0)
             have i₂ := b2e12 X0 (σ (M.op y x)) X1
             grind)
          | exact superpose b2e12 b2e1331
          | exact resolve b2e1331 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1355 : ∀ X0 X1 : G, (M.op (σ (M.op y x)) X0) = (M.op (M.op X1 (σ y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e59 (σ y) X1 (M.op (σ (M.op y x)) X0)
             have i₂ := b2e1331 X0
             grind)
          | exact superpose b2e1331 b2e59
          | exact resolve b2e59 b2e1331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e1331
        have b2e1381 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e303 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e303
          | exact resolve b2e303 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1450 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e303 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e303
        have b2e1472 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1381 X0 X1
             have i₂ := b2e29 X0 X1
             grind)
          | exact superpose b2e29 b2e1381
          | (have j0 := b2e1381 X0 X1
             grind)
          | exact resolve b2e1381 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e1381
        have b2e1485 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1472 X0 X1
             have i₂ := b2e30 X0 X1
             grind)
          | exact superpose b2e30 b2e1472
          | (have j0 := b2e1472 X0 X1
             grind)
          | exact resolve b2e1472 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1472
        have b2e1513 : ∀ X0 : G, (M.op (σ (M.op y x)) (M.op (σ y) X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 (σ (M.op y x)) x
             have i₂ := b2e1342 X0 x
             grind)
          | exact superpose b2e1342 b2e12
          | exact resolve b2e12 b2e1342
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1342
        have b2e1650 : (σ x) = (M.op (σ (M.op y x)) (σ (k y x))) := by
          first
          | (have i₁ := b2e1513 (σ x)
             have i₂ := b2e304
             grind)
          | exact superpose b2e304 b2e1513
          | exact resolve b2e1513 b2e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e304
        have b2e3093 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e804 (M.op x (σ y))
             have i₂ := b2e804 x
             grind)
          | exact superpose b2e804 b2e804
          | exact resolve b2e804 b2e804
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e804
        have b2e3149 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
        clear b2e3093
        have b2e3313 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e302 x y
             have i₂ := b2e3149
             grind)
          | exact superpose b2e3149 b2e302
          | (have j0 := b2e302 x y
             grind)
          | exact resolve b2e302 b2e3149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e302 b2e3149
        have b2e3343 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
        clear b2e3313
        have b2e3350 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b2e3343
             have r₂ := b2e353
             grind)
          | exact resolve b2e3343 b2e353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e353 b2e3343
        have b2e3357 : (σ x) = (σ (M.op y x)) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e3350
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e3350
          | exact resolve b2e3350 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e3350
        have b2e3527 : (M.op y x) = (τ (σ x)) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e13 (M.op y x)
             have i₂ := b2e3357
             grind)
          | exact superpose b2e3357 b2e13
          | exact resolve b2e13 b2e3357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3357
        have b2e3577 : x = (M.op y x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e3527
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e3527
          | exact resolve b2e3527 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3527
        have b2e3578 : x = (M.op y x) := by grind
        clear b2e3577
        have b2e3746 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X1 (σ y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e1355 X0 X1
             have i₂ := b2e3578
             grind)
          | exact superpose b2e3578 b2e1355
          | exact resolve b2e1355 b2e3578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1355
        have b2e3747 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1513 X0
             have i₂ := b2e3578
             grind)
          | exact superpose b2e3578 b2e1513
          | exact resolve b2e1513 b2e3578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1513
        have b2e3759 : x ≠ x ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e3578
             grind)
          | exact superpose b2e3578 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e3578
             grind)
          | exact resolve b2e15 b2e3578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3778 : (M.op x y) = (k y x) := by grind
        clear b2e3759
        have b2e3787 : y = (k y x) := by
          first
          | (have i₁ := b2e3778
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3778
          | exact resolve b2e3778 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3778
        have b2e4320 : (σ x) = (M.op (σ (M.op y x)) (σ y)) := by
          first
          | (have i₁ := b2e1650
             have i₂ := b2e3787
             grind)
          | exact superpose b2e3787 b2e1650
          | exact resolve b2e1650 b2e3787
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1650 b2e3787
        have b2e4333 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e4320
             have i₂ := b2e3578
             grind)
          | exact superpose b2e3578 b2e4320
          | exact resolve b2e4320 b2e3578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4320
        have b2e6515 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e1010 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1010
          | exact resolve b2e1010 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1010
        have b2e8671 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e1485 (σ X0) X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1485
        have b2e8672 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e8671 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8671
        have b2e8691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e8672 X0
             have j1 := b2e15 (σ X0) (σ X0)
             grind)
          | (have r₁ := b2e8672 X0
             have r₂ := b2e15 (σ X0) (σ X0)
             grind)
          | exact resolve b2e8672 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8672
        have b2e8724 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e8691 X0
             have i₂ := b2e18 X0 X0
             grind)
          | exact superpose b2e18 b2e8691
          | exact resolve b2e8691 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8691
        have b2e8750 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e8724 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e8724
          | exact resolve b2e8724 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e8790 : (σ y) = (M.op (σ x) (σ (k y y))) := by
          first
          | (have i₁ := b2e3747 (σ y)
             have i₂ := b2e8724 y
             grind)
          | exact superpose b2e8724 b2e3747
          | exact resolve b2e3747 b2e8724
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3747 b2e8724
        have b2e8864 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
          intro X0
          first
          | (have i₁ := b2e8750 X0
             have i₂ := b2e30 X0 (τ X0)
             grind)
          | exact superpose b2e30 b2e8750
          | exact resolve b2e8750 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e8750
        have b2e8873 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e8864 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e8864
          | exact resolve b2e8864 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8864
        have b2e10023 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e8790
             have i₂ := b2e8873 y
             grind)
          | exact superpose b2e8873 b2e8790
          | exact resolve b2e8790 b2e8873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8790 b2e8873
        have b2e10852 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ (M.op y y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e26 X0 (σ (M.op y y)) (σ x) X1
             have i₂ := b2e10023
             grind)
          | exact superpose b2e10023 b2e26
          | exact resolve b2e26 b2e10023
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e10870 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) := by
          intro X0
          first
          | (have i₁ := b2e10852 X0 x
             have i₂ := b2e3746 X0 x
             grind)
          | exact superpose b2e3746 b2e10852
          | exact resolve b2e10852 b2e3746
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3746 b2e10852
        have b2e43047 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e6515 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43495 : ∀ X0 : G, y ≠ X0 ∨ y = (k y (M.op y X0)) ∨ (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e43047 y (M.op y X0)
             have i₂ := b2e24 X0
             grind)
          | exact superpose b2e24 b2e43047
          | (have j0 := b2e43047 y (M.op y X0)
             grind)
          | (have r₁ := b2e43047 y (M.op y y)
             have r₂ := b2e24 y
             grind)
          | exact resolve b2e43047 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43047
        have b2e43957 : y = (k y (M.op y y)) ∨ y = (M.op y y) := by
          first
          | (have j0 := b2e43495 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43495
        have b2e44097 : (σ y) ≠ (σ y) ∨ (M.op (σ (M.op y y)) (σ y)) = (σ (k (M.op y y) y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e1450 (M.op y y) y
             have i₂ := b2e43957
             grind)
          | exact superpose b2e43957 b2e1450
          | (have j0 := b2e1450 (M.op y y) y
             grind)
          | exact resolve b2e1450 b2e43957
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1450 b2e43957
        have b2e44106 : (M.op (σ (M.op y y)) (σ y)) = (σ (k (M.op y y) y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e44097
        have b2e44114 : (M.op (σ x) (σ y)) = (σ (k (M.op y y) y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e44106
             have i₂ := b2e10870 (σ y)
             grind)
          | exact superpose b2e10870 b2e44106
          | exact resolve b2e44106 b2e10870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44106
        have b2e44123 : (σ x) = (σ (k (M.op y y) y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e44114
             have i₂ := b2e4333
             grind)
          | exact superpose b2e4333 b2e44114
          | exact resolve b2e44114 b2e4333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4333 b2e44114
        have b2e44130 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e44123
             have i₂ := b2e10870 (σ y)
             grind)
          | exact superpose b2e10870 b2e44123
          | exact resolve b2e44123 b2e10870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10870 b2e44123
        have b2e44134 : (σ x) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b2e44130
             have r₂ := b2e21
             grind)
          | exact resolve b2e44130 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44130
        have b2e44752 : (τ (σ x)) = (k (M.op y y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e13 (k (M.op y y) y)
             have i₂ := b2e44134
             grind)
          | exact superpose b2e44134 b2e13
          | exact resolve b2e13 b2e44134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44134
        have b2e44867 : x = (k (M.op y y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e44752
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e44752
          | exact resolve b2e44752 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44752
        have b2e45372 : x ≠ y ∨ (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e967 (M.op y y) y
             have i₂ := b2e44867
             grind)
          | exact superpose b2e44867 b2e967
          | (have j0 := b2e967 (M.op y y) y
             grind)
          | exact resolve b2e967 b2e44867
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e967
        have b2e45401 : x = (M.op (M.op y y) y) ∨ x = (M.op y y) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e6515 (M.op y y) y
             have i₂ := b2e44867
             grind)
          | exact superpose b2e44867 b2e6515
          | (have j0 := b2e6515 (M.op y y) y
             grind)
          | exact resolve b2e6515 b2e44867
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6515 b2e44867
        have b2e45402 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e45401
             have i₂ := b2e27 y y
             grind)
          | exact superpose b2e27 b2e45401
          | exact resolve b2e45401 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45401
        have b2e45403 : x = (M.op y y) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) := by grind
        clear b2e45402
        have b2e45413 : y = (M.op y y) ∨ x ≠ y ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e45372
             have i₂ := b2e24 y
             grind)
          | exact superpose b2e24 b2e45372
          | exact resolve b2e45372 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45372
        have b2e45414 : y = (M.op y y) ∨ x ≠ y ∨ y = (M.op (M.op y y) y) := by grind
        clear b2e45413
        have b2e45419 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e45403
             have i₂ := b2e27 y y
             grind)
          | exact superpose b2e27 b2e45403
          | exact resolve b2e45403 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45403
        have b2e45420 : x = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b2e45419
        have b2e45424 : y = (M.op y y) ∨ y = (M.op y y) ∨ x ≠ y := by
          first
          | (have i₁ := b2e45414
             have i₂ := b2e27 y y
             grind)
          | exact superpose b2e27 b2e45414
          | exact resolve b2e45414 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e45414
        have b2e45425 : x ≠ y ∨ y = (M.op y y) := by grind
        clear b2e45424
        have b2e46558 : y = (M.op y x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e24 y
             have i₂ := b2e45420
             grind)
          | exact superpose b2e45420 b2e24
          | exact resolve b2e24 b2e45420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e45420
        have b2e46651 : x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e46558
             have i₂ := b2e3578
             grind)
          | exact superpose b2e3578 b2e46558
          | exact resolve b2e46558 b2e3578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3578 b2e46558
        have b2e46658 : y = (M.op y y) := by
          first
          | (have r₁ := b2e46651
             have r₂ := b2e45425
             grind)
          | exact resolve b2e46651 b2e45425
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45425 b2e46651
        have b2e47321 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e10023
             have i₂ := b2e46658
             grind)
          | exact superpose b2e46658 b2e10023
          | exact resolve b2e10023 b2e46658
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10023 b2e46658
        have b2e47418 : False := by grind
        exact b2e47418
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e35 : x ≠ x ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 y x
             grind)
          | (have r₁ := b3e15 y x
             have r₂ := b3e21
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : (M.op x y) = (k y x) := by grind
        clear b3e35
        have b3e37 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b3e33
        have b3e38 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e37
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e37
          | exact resolve b3e37 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e42 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) := by
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
        have b3e43 : y = (M.op x y) ∨ x = (k x y) := by grind
        clear b3e42
        have b3e45 : x = (k x y) := by
          first
          | (have r₁ := b3e43
             have r₂ := b3e20
             grind)
          | exact resolve b3e43 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e98 : (σ x) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e15
          | (have j0 := b3e15 (σ y) (σ x)
             grind)
          | exact resolve b3e15 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e101 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e98
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e98
          | exact resolve b3e98 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e98
        have b3e102 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e101
        have b3e105 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e102
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e102
          | exact resolve b3e102 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e105
             have i₂ := b3e36
             grind)
          | exact superpose b3e36 b3e105
          | exact resolve b3e105 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e105
        have b3e108 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b3e107
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e107
          | exact resolve b3e107 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e107
        have b3e109 : False := by grind
        exact b3e109
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : x ≠ x ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y x
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : (M.op x y) = (k y x) := by grind
          clear b4e39
          have b4e41 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b4e36
          have b4e42 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e41
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e41
            | exact resolve b4e41 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e43 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e42
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e42
            | exact resolve b4e42 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e42
          have b4e44 : False := by grind
          exact b4e44
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e42 : x ≠ x ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b5e16 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y x
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : (M.op x y) = (k y x) := by grind
          clear b5e42
          have b5e47 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) := by
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
          have b5e48 : y = (M.op x y) ∨ x = (k x y) := by grind
          clear b5e47
          have b5e49 : x = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e252 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e53 x y
               grind)
            | exact superpose b5e53 b5e24
            | (have j1 := b5e53 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e53 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e53 y x
               grind)
            | exact resolve b5e24 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e269 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e252
          have b5e275 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e269
               have r₂ := b5e23
               grind)
            | exact resolve b5e269 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e269
          have b5e282 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e275
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e275
            | exact resolve b5e275 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e275
          have b5e285 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e282
               grind)
            | exact superpose b5e282 b5e23
            | exact resolve b5e23 b5e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e286 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ y) (σ x)
               have i₂ := b5e282
               grind)
            | exact superpose b5e282 b5e13
            | exact resolve b5e13 b5e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e348 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e286 (σ y)
               have i₂ := b5e282
               grind)
            | exact superpose b5e282 b5e286
            | exact resolve b5e286 b5e282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e282 b5e286
          have b5e483 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e53 y x
               have i₂ := b5e348
               grind)
            | exact superpose b5e348 b5e53
            | (have j0 := b5e53 y x
               grind)
            | exact resolve b5e53 b5e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e348
          have b5e502 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e483
               have r₂ := b5e23
               grind)
            | exact resolve b5e483 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e483
          have b5e507 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b5e502
               have r₂ := b5e285
               grind)
            | exact resolve b5e502 b5e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e285 b5e502
          have b5e511 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b5e507
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e507
            | exact resolve b5e507 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e507
          have b5e531 : (M.op x y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (M.op x y)
               have i₂ := b5e511
               grind)
            | exact superpose b5e511 b5e14
            | exact resolve b5e14 b5e511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e511
          have b5e548 : y = (M.op x y) := by
            first
            | (have i₁ := b5e531
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e531
            | exact resolve b5e531 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e531
          have b5e549 : False := by grind
          exact b5e549
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X3 (M.op (M.op X1 X2) X0) X2
             have i₂ := b6e12 X0 X2 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b6e34 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b6e31
        have b6e35 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
        have b6e40 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b6e40
        have b6e44 : (σ x) = (σ (k x y)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e43
          | exact resolve b6e43 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e45 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e44
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e44
          | exact resolve b6e44 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e58 : (σ x) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e24 (σ x)
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e24
          | exact resolve b6e24 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e60 : (σ x) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e35
             grind)
          | exact superpose b6e35 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e15 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e60
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e60
          | exact resolve b6e60 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e63 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e62
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e62
          | exact resolve b6e62 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e64 : (σ y) = (σ (k y x)) := by
          first
          | (have r₁ := b6e63
             have r₂ := b6e45
             grind)
          | exact resolve b6e63 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45 b6e63
        have b6e79 : ∀ X0 X1 X4 : G, (M.op (M.op X1 X0) (M.op X0 X4)) = X4 := by
          intro X0 X1 X4
          first
          | (have i₁ := b6e12 X4 (M.op X1 X0) (M.op (M.op x x) X1)
             have i₂ := b6e25 X1 x x X0
             grind)
          | exact superpose b6e25 b6e12
          | exact resolve b6e12 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e84 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e64
             grind)
          | exact superpose b6e64 b6e13
          | exact resolve b6e13 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e85 : y = (k y x) := by
          first
          | (have i₁ := b6e84
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e84
          | exact resolve b6e84 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e112 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e85
             grind)
          | exact superpose b6e85 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e113 : y = (M.op y x) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e112
             have r₂ := b6e20
             grind)
          | exact resolve b6e112 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e112
        have b6e115 : y = (M.op y x) := by
          first
          | (have r₁ := b6e113
             have r₂ := b6e21
             grind)
          | exact resolve b6e113 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e113
        have b6e127 : ∀ X0 : G, (M.op x (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e115
             grind)
          | exact superpose b6e115 b6e12
          | exact resolve b6e12 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e172 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (M.op (σ X0) X2)) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 (σ X0) (σ X1)
             have i₂ := b6e55 X0 X1
             grind)
          | exact superpose b6e55 b6e12
          | (have j1 := b6e55 X0 X1
             grind)
          | exact resolve b6e12 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e173 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (σ X1) (σ X0)
             have i₂ := b6e55 X0 X1
             grind)
          | exact superpose b6e55 b6e15
          | (have j0 := b6e15 (σ X1) (σ X0)
             have j1 := b6e55 X0 X1
             grind)
          | (have r₁ := b6e15 (σ X1) (σ X0)
             have r₂ := b6e55 X0 X1
             grind)
          | (have r₁ := b6e15 (σ X0) (σ X1)
             have r₂ := b6e55 X0 X1
             grind)
          | exact resolve b6e15 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e184 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e173 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e173
        have b6e188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e184 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e184
          | (have j0 := b6e184 X0 X1
             grind)
          | exact resolve b6e184 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e184
        have b6e227 : x = (M.op x y) := by
          first
          | (have i₁ := b6e127 x
             have i₂ := b6e115
             grind)
          | exact superpose b6e115 b6e127
          | exact resolve b6e127 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e247 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e79 x y X0
             have i₂ := b6e115
             grind)
          | exact superpose b6e115 b6e79
          | exact resolve b6e79 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e252 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e79 (σ x) X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e79
          | exact resolve b6e79 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e275 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e227
             grind)
          | exact superpose b6e227 b6e23
          | exact resolve b6e23 b6e227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e402 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e58
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e58 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e422 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e402
             have r₂ := b6e21
             grind)
          | exact resolve b6e402 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e402
        have b6e423 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
          first
          | (have r₁ := b6e422
             have r₂ := b6e20
             grind)
          | exact resolve b6e422 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e422
        have b6e424 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e423
             have i₂ := b6e227
             grind)
          | exact superpose b6e227 b6e423
          | exact resolve b6e423 b6e227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e227 b6e423
        have b6e426 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e424
             grind)
          | exact superpose b6e424 b6e35
          | exact resolve b6e35 b6e424
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e424
        have b6e483 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e426
             grind)
          | exact superpose b6e426 b6e13
          | exact resolve b6e13 b6e426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e484 : ∀ X0 : G, (σ (k (k x y) X0)) = (k (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 (k x y) X0
             have i₂ := b6e426
             grind)
          | exact superpose b6e426 b6e18
          | exact resolve b6e18 b6e426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e485 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 (k x y)
             have i₂ := b6e426
             grind)
          | exact superpose b6e426 b6e18
          | exact resolve b6e18 b6e426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e426
        have b6e494 : ∀ X0 : G, (σ (k X0 (k x y))) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b6e485 X0
             have i₂ := b6e18 X0 x
             grind)
          | exact superpose b6e18 b6e485
          | exact resolve b6e485 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e485
        have b6e495 : ∀ X0 : G, (σ (k (k x y) X0)) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b6e484 X0
             have i₂ := b6e18 x X0
             grind)
          | exact superpose b6e18 b6e484
          | exact resolve b6e484 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e484
        have b6e496 : x = (k x y) := by
          first
          | (have i₁ := b6e483
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e483
          | exact resolve b6e483 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e483
        have b6e1123 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (M.op X0 (σ x)) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e15 (M.op X0 (σ x)) (σ y)
             have i₂ := b6e252 X0
             grind)
          | exact superpose b6e252 b6e15
          | (have j0 := b6e15 (M.op X0 (σ x)) (σ y)
             grind)
          | (have r₁ := b6e15 (M.op X0 (σ x)) (σ y)
             have r₂ := b6e252 X0
             grind)
          | exact resolve b6e15 b6e252
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1140 : ∀ X0 : G, (k (M.op X0 (σ x)) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have j0 := b6e1123 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1123
        have b6e1538 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 (k x y))) ∨ (M.op (k x y) X0) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
          intro X0
          first
          | (have i₁ := b6e494 X0
             have i₂ := b6e17 X0 (k x y)
             grind)
          | exact superpose b6e17 b6e494
          | (have j1 := b6e17 X0 (k x y)
             grind)
          | exact resolve b6e494 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e494
        have b6e1579 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op (k x y) X0) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
          intro X0
          first
          | (have i₁ := b6e1538 X0
             have i₂ := b6e496
             grind)
          | exact superpose b6e496 b6e1538
          | (have j0 := b6e1538 X0
             grind)
          | exact resolve b6e1538 b6e496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1538
        have b6e1582 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (k x y) = (M.op X0 (k x y)) := by
          intro X0
          first
          | (have i₁ := b6e1579 X0
             have i₂ := b6e496
             grind)
          | exact superpose b6e496 b6e1579
          | (have j0 := b6e1579 X0
             grind)
          | exact resolve b6e1579 b6e496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1579
        have b6e1585 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op x X0) = X0 ∨ x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e1582 X0
             have i₂ := b6e496
             grind)
          | exact superpose b6e496 b6e1582
          | (have j0 := b6e1582 X0
             grind)
          | exact resolve b6e1582 b6e496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1582
        have b6e2866 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = X1 ∨ (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = (M.op X0 (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e172 (τ X0) X1 X2
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e172
          | exact resolve b6e172 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e172
        have b6e2971 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (M.op X0 (M.op X0 X1)) = X1 ∨ (σ X2) = (M.op X0 (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2866 X0 X1 X2
             have i₂ := b6e27 X0 X2
             grind)
          | exact superpose b6e27 b6e2866
          | (have j0 := b6e2866 X0 X1 X2
             grind)
          | exact resolve b6e2866 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2866
        have b6e3225 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e188 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e188
          | exact resolve b6e188 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e188
        have b6e3374 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e3225 X0 X1
             have i₂ := b6e28 X0 X1
             grind)
          | exact superpose b6e28 b6e3225
          | (have j0 := b6e3225 X0 X1
             grind)
          | exact resolve b6e3225 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3225
        have b6e3410 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e3374 X0 X1
             have i₂ := b6e27 X0 X1
             grind)
          | exact superpose b6e27 b6e3374
          | (have j0 := b6e3374 X0 X1
             grind)
          | exact resolve b6e3374 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e3374
        have b6e5720 : (σ (k x x)) = (σ (M.op (k x y) x)) ∨ (k x y) = (M.op x (k x y)) ∨ x = (M.op (k x y) x) := by
          first
          | (have i₁ := b6e495 x
             have i₂ := b6e1585 (k x y)
             grind)
          | exact superpose b6e1585 b6e495
          | (have j1 := b6e1585 (k x y)
             grind)
          | exact resolve b6e495 b6e1585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e495 b6e1585
        have b6e5783 : (σ (k x x)) = (σ (M.op x x)) ∨ (k x y) = (M.op x (k x y)) ∨ x = (M.op (k x y) x) := by
          first
          | (have i₁ := b6e5720
             have i₂ := b6e496
             grind)
          | exact superpose b6e496 b6e5720
          | exact resolve b6e5720 b6e496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5720
        have b6e5785 : x = (M.op x x) ∨ (σ (k x x)) = (σ (M.op x x)) ∨ x = (M.op (k x y) x) := by
          first
          | (have i₁ := b6e5783
             have i₂ := b6e496
             grind)
          | exact superpose b6e496 b6e5783
          | exact resolve b6e5783 b6e496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5783
        have b6e5787 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (k x x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e5785
             have i₂ := b6e496
             grind)
          | exact superpose b6e496 b6e5785
          | exact resolve b6e5785 b6e496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e496 b6e5785
        have b6e5788 : (σ (k x x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b6e5787
        have b6e5886 : (k x x) = (τ (σ (M.op x x))) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e5788
             grind)
          | exact superpose b6e5788 b6e13
          | exact resolve b6e13 b6e5788
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5788
        have b6e5948 : (M.op x x) = (k x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e5886
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e5886
          | exact resolve b6e5886 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5886
        have b6e5950 : (M.op x x) = (k x x) := by
          first
          | (have j1 := b6e15 x x
             grind)
          | (have r₁ := b6e5948
             have r₂ := b6e15 x x
             grind)
          | exact resolve b6e5948 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5948
        have b6e11670 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = X2 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2971 X0 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e2971
          | (have j0 := b6e2971 X1 X2 X2
             grind)
          | exact resolve b6e2971 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2971
        have b6e12561 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (M.op y y) ∨ (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e11670 X0 y x
             have i₂ := b6e115
             grind)
          | exact superpose b6e115 b6e11670
          | (have j0 := b6e11670 X0 y x
             grind)
          | exact resolve b6e11670 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e11670
        have b6e13584 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e3410 (σ X0) X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3410
        have b6e13585 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e13584 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13584
        have b6e13615 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e13585 X0
             have j1 := b6e15 (σ X0) (σ X0)
             grind)
          | (have r₁ := b6e13585 X0
             have r₂ := b6e15 (σ X0) (σ X0)
             grind)
          | exact resolve b6e13585 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13585
        have b6e13648 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e13615 X0
             have i₂ := b6e18 X0 X0
             grind)
          | exact superpose b6e18 b6e13615
          | exact resolve b6e13615 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13615
        have b6e13674 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e13648 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e13648
          | exact resolve b6e13648 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e13739 : (M.op (σ y) (σ (k x x))) = (k (σ (k x x)) (σ y)) := by
          first
          | (have i₁ := b6e1140 (σ x)
             have i₂ := b6e13648 x
             grind)
          | exact superpose b6e13648 b6e1140
          | exact resolve b6e1140 b6e13648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1140
        have b6e13742 : (σ y) = (M.op (σ (k x x)) (σ y)) := by
          first
          | (have i₁ := b6e252 (σ x)
             have i₂ := b6e13648 x
             grind)
          | exact superpose b6e13648 b6e252
          | exact resolve b6e252 b6e13648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e13748 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (k X0 X0)) X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 (σ X0) (σ X0)
             have i₂ := b6e13648 X0
             grind)
          | exact superpose b6e13648 b6e12
          | exact resolve b6e12 b6e13648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e13786 : (σ y) = (M.op (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b6e13742
             have i₂ := b6e5950
             grind)
          | exact superpose b6e5950 b6e13742
          | exact resolve b6e13742 b6e5950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13742
        have b6e13789 : (M.op (σ y) (σ (k x x))) = (σ (k (k x x) y)) := by
          first
          | (have i₁ := b6e13739
             have i₂ := b6e18 (k x x) y
             grind)
          | exact superpose b6e18 b6e13739
          | exact resolve b6e13739 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13739
        have b6e13825 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
          intro X0
          first
          | (have i₁ := b6e13674 X0
             have i₂ := b6e28 X0 (τ X0)
             grind)
          | exact superpose b6e28 b6e13674
          | exact resolve b6e13674 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e13674
        have b6e13828 : (M.op (σ y) (σ (M.op x x))) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b6e13789
             have i₂ := b6e5950
             grind)
          | exact superpose b6e5950 b6e13789
          | exact resolve b6e13789 b6e5950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5950 b6e13789
        have b6e13840 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b6e13825 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e13825
          | exact resolve b6e13825 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13825
        have b6e14472 : (σ y) ≠ (σ y) ∨ (σ (M.op x x)) = (M.op (σ y) (σ (M.op x x))) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by
          first
          | (have i₁ := b6e16 (σ y) (σ (M.op x x))
             have i₂ := b6e13786
             grind)
          | exact superpose b6e13786 b6e16
          | (have j0 := b6e16 (σ y) (σ (M.op x x))
             grind)
          | (have r₁ := b6e16 (σ y) (σ (M.op x x))
             have r₂ := b6e13786
             grind)
          | exact resolve b6e16 b6e13786
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e14508 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op x x))) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by grind
        clear b6e14472
        have b6e14513 : (σ (M.op x x)) = (σ (k (M.op x x) y)) ∨ (σ y) = (k (σ y) (σ (M.op x x))) := by
          first
          | (have i₁ := b6e14508
             have i₂ := b6e13828
             grind)
          | exact superpose b6e13828 b6e14508
          | exact resolve b6e14508 b6e13828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e14508
        have b6e14521 : (σ y) = (σ (k y (M.op x x))) ∨ (σ (M.op x x)) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b6e14513
             have i₂ := b6e18 y (M.op x x)
             grind)
          | exact superpose b6e18 b6e14513
          | exact resolve b6e14513 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e14513
        have b6e16156 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b6e13748 X0 (σ (k X0 X0))
             have i₂ := b6e13648 (k X0 X0)
             grind)
          | exact superpose b6e13648 b6e13748
          | exact resolve b6e13748 b6e13648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13648 b6e13748
        have b6e16265 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b6e16156 X0
             have i₂ := b6e13840 (k X0 X0)
             grind)
          | exact superpose b6e13840 b6e16156
          | exact resolve b6e16156 b6e13840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16156
        have b6e16365 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b6e16265 X0
             have i₂ := b6e13840 X0
             grind)
          | exact superpose b6e13840 b6e16265
          | exact resolve b6e16265 b6e13840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13840 b6e16265
        have b6e16426 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e16365 X0
             have i₂ := b6e79 X0 X0 X0
             grind)
          | (have i₁ := b6e16365 X0
             have i₂ := b6e79 X0 x (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact superpose b6e79 b6e16365
          | exact resolve b6e16365 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16365
        have b6e16912 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e79 (σ X0) X1 (σ X0)
             have i₂ := b6e16426 X0
             grind)
          | exact superpose b6e16426 b6e79
          | exact resolve b6e79 b6e16426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79 b6e16426
        have b6e32241 : (σ (M.op x x)) ≠ (σ (k (M.op x x) y)) ∨ (M.op (σ (M.op x x)) (σ y)) = (k (σ y) (σ (M.op x x))) := by
          first
          | (have i₁ := b6e15 (σ y) (σ (M.op x x))
             have i₂ := b6e13828
             grind)
          | exact superpose b6e13828 b6e15
          | (have j0 := b6e15 (σ y) (σ (M.op x x))
             grind)
          | exact resolve b6e15 b6e13828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13828
        have b6e32291 : (σ (k y (M.op x x))) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ (M.op x x)) ≠ (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b6e32241
             have i₂ := b6e18 y (M.op x x)
             grind)
          | exact superpose b6e18 b6e32241
          | exact resolve b6e32241 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32241
        have b6e32313 : (σ y) = (σ (k y (M.op x x))) ∨ (σ (M.op x x)) ≠ (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b6e32291
             have i₂ := b6e13786
             grind)
          | exact superpose b6e13786 b6e32291
          | exact resolve b6e32291 b6e13786
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13786 b6e32291
        have b6e32321 : (σ y) = (σ (k y (M.op x x))) := by
          first
          | (have r₁ := b6e32313
             have r₂ := b6e14521
             grind)
          | exact resolve b6e32313 b6e14521
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e14521 b6e32313
        have b6e32653 : (σ y) = (σ (M.op y (M.op x x))) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b6e32321
             have i₂ := b6e12561 (M.op x x)
             grind)
          | exact superpose b6e12561 b6e32321
          | (have j1 := b6e12561 (M.op x x)
             grind)
          | exact resolve b6e32321 b6e12561
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12561 b6e32321
        have b6e32805 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b6e32653
             have i₂ := b6e247 x
             grind)
          | exact superpose b6e247 b6e32653
          | exact resolve b6e32653 b6e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32653
        have b6e32814 : x = (M.op y y) ∨ (M.op x x) = (M.op y (M.op x x)) := by
          first
          | (have r₁ := b6e32805
             have r₂ := b6e275
             grind)
          | exact resolve b6e32805 b6e275
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32805
        have b6e32820 : x = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e32814
             have i₂ := b6e247 x
             grind)
          | exact superpose b6e247 b6e32814
          | exact resolve b6e32814 b6e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32814
        have b6e33421 : x = (M.op y x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e247 x
             have i₂ := b6e32820
             grind)
          | exact superpose b6e32820 b6e247
          | exact resolve b6e247 b6e32820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e247 b6e32820
        have b6e33497 : x = (M.op y y) := by
          first
          | (have r₁ := b6e33421
             have r₂ := b6e21
             grind)
          | exact resolve b6e33421 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33421
        have b6e33690 : y = (M.op x x) := by
          first
          | (have i₁ := b6e127 y
             have i₂ := b6e33497
             grind)
          | exact superpose b6e33497 b6e127
          | exact resolve b6e127 b6e33497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e127 b6e33497
        have b6e34083 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e16912 x X0
             have i₂ := b6e33690
             grind)
          | exact superpose b6e33690 b6e16912
          | exact resolve b6e16912 b6e33690
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16912 b6e33690
        have b6e34134 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e34083 x
             have i₂ := b6e252 x
             grind)
          | exact superpose b6e252 b6e34083
          | exact resolve b6e34083 b6e252
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e252 b6e34083
        have b6e34147 : False := by grind
        exact b6e34147
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op (M.op X1 X2) X0) X2
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X1)) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X3 (M.op X2 X1)) X0) X1 X2
               have i₂ := b7e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) (σ x)
               grind)
            | (have r₁ := b7e16 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b7e36
          have b7e40 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e39
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e39
            | exact resolve b7e39 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e49 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e52 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
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
          have b7e69 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
          have b7e70 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e22
               grind)
            | exact resolve b7e69 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e72 : x = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e21
               grind)
            | exact resolve b7e70 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e75 : (σ y) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e40
               grind)
            | exact superpose b7e40 b7e23
            | exact resolve b7e23 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e104 : ∀ X0 X1 X4 : G, (M.op (M.op X1 X0) (M.op X0 X4)) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e13 X4 (M.op X1 X0) (M.op (M.op x x) X1)
               have i₂ := b7e26 X1 x x X0
               grind)
            | exact superpose b7e26 b7e13
            | exact resolve b7e13 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e112 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e27 X0 y x X1
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e27
            | exact resolve b7e27 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e146 : (σ y) ≠ (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e75
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e75
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e75 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e147 : (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e146
               have r₂ := b7e21
               grind)
            | exact resolve b7e146 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e146
          have b7e148 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e147
               have r₂ := b7e22
               grind)
            | exact resolve b7e147 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e147
          have b7e252 : ∀ X0 : G, y = (M.op (M.op X0 x) x) := by
            intro X0
            first
            | (have i₁ := b7e104 x X0 y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e104
            | exact resolve b7e104 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e104
          have b7e266 : y = (M.op y x) := by
            first
            | (have i₁ := b7e252 x
               have i₂ := b7e112 x x
               grind)
            | exact superpose b7e112 b7e252
            | exact resolve b7e252 b7e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112 b7e252
          have b7e269 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b7e148
               have i₂ := b7e266
               grind)
            | exact superpose b7e266 b7e148
            | exact resolve b7e148 b7e266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148 b7e266
          have b7e281 : False := by grind
          exact b7e281
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e158 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e44 x y
               grind)
            | exact superpose b8e44 b8e24
            | (have j1 := b8e44 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e44 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e44 y x
               grind)
            | exact resolve b8e24 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e174 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e158
          have b8e179 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e174
               have r₂ := b8e23
               grind)
            | exact resolve b8e174 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e186 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e179
               grind)
            | exact superpose b8e179 b8e20
            | exact resolve b8e20 b8e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179
          have b8e310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e186
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e186
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e186 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e311 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e310
          have b8e312 : y = (M.op x y) := by
            first
            | (have r₁ := b8e311
               have r₂ := b8e22
               grind)
            | exact resolve b8e311 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311
          have b8e313 : False := by grind
          exact b8e313

/-- `Equation138`: `x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then Y else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_y_pxy_pyx_Equation138 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law138 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law138.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ y) ≠ (σ y) := by
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
      have b0e23 : False := by grind
      exact b0e23
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e32 : y ≠ y ∨ y = (k x y) := by
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
        have b1e34 : y = (k x y) := by grind
        clear b1e32
        have b1e46 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e46
        have b1e53 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e21
             grind)
          | exact resolve b1e50 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e54 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b1e55 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e34
             grind)
          | exact superpose b1e34 b1e54
          | exact resolve b1e54 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e54
        have b1e56 : False := by grind
        exact b1e56
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X1)) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op (M.op X3 (M.op X2 X1)) X0) X1 X2
             have i₂ := b2e12 X0 (M.op X2 X1) X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 y) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e24 (M.op (M.op X1 y) X0)
             have i₂ := b2e12 X0 y X1
             grind)
          | exact superpose b2e12 b2e24
          | exact resolve b2e24 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (M.op y X0) y
             have i₂ := b2e24 X0
             grind)
          | exact superpose b2e24 b2e12
          | exact resolve b2e12 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : y ≠ y ∨ y = (k x y) := by
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
        have b2e31 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (M.op y X0) = (k y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e15 y (M.op y X0)
             have i₂ := b2e24 X0
             grind)
          | exact superpose b2e24 b2e15
          | (have j0 := b2e15 y X0
             grind)
          | exact resolve b2e15 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : y = (k x y) := by grind
        clear b2e29
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
        have b2e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e38 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (k (M.op X1 y) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (M.op X1 y) X0
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e15
          | (have j0 := b2e15 y X0
             grind)
          | exact resolve b2e15 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e45 : y ≠ y ∨ x = (M.op y x) ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : (M.op y x) = (k y x) ∨ x = (M.op y x) := by grind
        clear b2e45
        have b2e59 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X1 X0) (M.op y X1)
             have i₂ := b2e28 X1 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e79 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
        have b2e88 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e34 X1 X0
             grind)
          | exact superpose b2e34 b2e13
          | exact resolve b2e13 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e98 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e59 X2 X1 (M.op (M.op X3 X2) X0)
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e59
          | exact resolve b2e59 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e183 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X1 ∨ (k (M.op X2 (M.op X3 X0)) X1) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e15 (M.op X2 (M.op X3 X0)) X1
             have i₂ := b2e26 X1 X0 X3 X2
             grind)
          | exact superpose b2e26 b2e15
          | (have j0 := b2e15 X0 X1
             grind)
          | exact resolve b2e15 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e206 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e79 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e79
          | exact resolve b2e79 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e238 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e88 (k X0 (τ X1)) X2
             have i₂ := b2e34 X1 X0
             grind)
          | exact superpose b2e34 b2e88
          | exact resolve b2e88 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e273 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e64 y x
             grind)
          | exact superpose b2e64 b2e21
          | (have j1 := b2e64 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e64 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e64 x y
             grind)
          | exact resolve b2e21 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e275 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X1) (σ X0)
             have i₂ := b2e64 X0 X1
             grind)
          | exact superpose b2e64 b2e15
          | (have j0 := b2e15 (σ X1) (σ X0)
             have j1 := b2e64 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X1) (σ X0)
             have r₂ := b2e64 X0 X1
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e64 X0 X1
             grind)
          | exact resolve b2e15 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e276 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X0) (σ X1)
             have i₂ := b2e64 X0 X1
             grind)
          | exact superpose b2e64 b2e16
          | (have j0 := b2e16 (σ X0) (σ X1)
             have j1 := b2e64 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X0) (σ X1)
             have r₂ := b2e64 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e64 X0 X1
             grind)
          | exact resolve b2e16 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e284 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e64 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e286 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e284 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e284
        have b2e287 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e276 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e276
        have b2e288 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e287 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e287
        have b2e289 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e275 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e275
        have b2e290 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e273
        have b2e293 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e288 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e288
          | (have j0 := b2e288 X0 X1
             grind)
          | exact resolve b2e288 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e288
        have b2e294 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e289 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e289
          | (have j0 := b2e289 X0 X1
             grind)
          | exact resolve b2e289 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e289
        have b2e295 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e290
             have r₂ := b2e22
             grind)
          | exact resolve b2e290 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e290
        have b2e301 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e295
             have i₂ := b2e32
             grind)
          | exact superpose b2e32 b2e295
          | exact resolve b2e295 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e295
        have b2e303 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e301
             grind)
          | exact superpose b2e301 b2e22
          | exact resolve b2e22 b2e301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e304 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 (σ x) (σ y)
             have i₂ := b2e301
             grind)
          | exact superpose b2e301 b2e12
          | exact resolve b2e12 b2e301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e313 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e59 (σ y) X0 (σ x)
             have i₂ := b2e301
             grind)
          | exact superpose b2e301 b2e59
          | exact resolve b2e59 b2e301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e349 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e304 (σ x)
             have i₂ := b2e301
             grind)
          | exact superpose b2e301 b2e304
          | exact resolve b2e304 b2e301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e301 b2e304
        have b2e389 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e64 x y
             have i₂ := b2e349
             grind)
          | exact superpose b2e349 b2e64
          | (have j0 := b2e64 x y
             grind)
          | exact resolve b2e64 b2e349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64 b2e349
        have b2e406 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e389
             have r₂ := b2e22
             grind)
          | exact resolve b2e389 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e389
        have b2e412 : (σ x) = (σ (k y x)) := by
          first
          | (have r₁ := b2e406
             have r₂ := b2e303
             grind)
          | exact resolve b2e406 b2e303
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e406
        have b2e435 : (k y x) = (τ (σ x)) := by
          first
          | (have i₁ := b2e13 (k y x)
             have i₂ := b2e412
             grind)
          | exact superpose b2e412 b2e13
          | exact resolve b2e13 b2e412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412
        have b2e452 : x = (k y x) := by
          first
          | (have i₁ := b2e435
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e435
          | exact resolve b2e435 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e435
        have b2e478 : x = (M.op y x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e47
             have i₂ := b2e452
             grind)
          | exact superpose b2e452 b2e47
          | exact resolve b2e47 b2e452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e452
        have b2e480 : x = (M.op y x) := by grind
        clear b2e478
        have b2e527 : ∀ X0 X1 : G, x ≠ x ∨ x = (k (M.op X0 (M.op X1 y)) x) := by
          intro X0 X1
          first
          | (have i₁ := b2e183 y x X0 X1
             have i₂ := b2e480
             grind)
          | exact superpose b2e480 b2e183
          | (have j0 := b2e183 y x X0 X1
             grind)
          | (have r₁ := b2e183 y x x x
             have r₂ := b2e480
             grind)
          | exact resolve b2e183 b2e480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e183 b2e480
        have b2e528 : ∀ X0 X1 : G, x = (k (M.op X0 (M.op X1 y)) x) := by
          intro X0 X1
          first
          | (have j0 := b2e527 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e527
        have b2e587 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e286 (τ X0)
             have i₂ := b2e34 X0 (τ X0)
             grind)
          | exact superpose b2e34 b2e286
          | (have j0 := b2e286 (τ X0)
             grind)
          | exact resolve b2e286 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e286
        have b2e589 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e587 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e587
          | (have j0 := b2e587 X0
             grind)
          | exact resolve b2e587 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e587
        have b2e591 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e589 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e589
          | (have j0 := b2e589 X0
             grind)
          | exact resolve b2e589 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e589
        have b2e739 : ∀ X0 : G, x = (k (M.op X0 y) x) := by
          intro X0
          first
          | (have i₁ := b2e528 X0 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e528
          | exact resolve b2e528 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e528
        have b2e862 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k (τ X0) X1)) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e294 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e294
          | (have j0 := b2e294 X1 (τ X0)
             grind)
          | exact resolve b2e294 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e294
        have b2e900 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k (τ X0) X1)) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e862 X0 X1
             have i₂ := b2e33 X0 X1
             grind)
          | exact superpose b2e33 b2e862
          | (have j0 := b2e862 X0 X1
             grind)
          | exact resolve b2e862 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e862
        have b2e906 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (k X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e900 X0 X1
             have i₂ := b2e33 X0 X1
             grind)
          | exact superpose b2e33 b2e900
          | (have j0 := b2e900 X0 X1
             grind)
          | exact resolve b2e900 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e900
        have b2e1016 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e293 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e293
          | exact resolve b2e293 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1022 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e293 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e293
          | exact resolve b2e293 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1041 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X1) (σ X0)
             have i₂ := b2e293 X0 X1
             grind)
          | exact superpose b2e293 b2e16
          | (have j0 := b2e16 (σ X1) (σ X0)
             have j1 := b2e293 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e293 X0 X1
             grind)
          | exact resolve b2e16 b2e293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1071 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e293 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e293
        have b2e1080 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b2e1041 X0 X1
             have j1 := b2e16 (σ X1) (σ X0)
             grind)
          | (have r₁ := b2e1041 X0 X1
             have r₂ := b2e16 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e1041 X0 X1
             have r₂ := b2e16 (σ X1) (σ X0)
             grind)
          | exact resolve b2e1041 b2e16
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1041
        have b2e1085 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1022 X0 X1
             have i₂ := b2e33 X0 X1
             grind)
          | exact superpose b2e33 b2e1022
          | (have j0 := b2e1022 X0 X1
             grind)
          | exact resolve b2e1022 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1022
        have b2e1087 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e1016 X0 X1
             have i₂ := b2e34 X0 X1
             grind)
          | exact superpose b2e34 b2e1016
          | (have j0 := b2e1016 X0 X1
             grind)
          | exact resolve b2e1016 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1016
        have b2e1096 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e1080 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e1080
          | (have j0 := b2e1080 X0 X1
             grind)
          | exact resolve b2e1080 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1080
        have b2e1100 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e1085 X0 X1
             have i₂ := b2e34 X0 X1
             grind)
          | exact superpose b2e34 b2e1085
          | (have j0 := b2e1085 X0 X1
             grind)
          | exact resolve b2e1085 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1085
        have b2e1102 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e1087 X0 X1
             have i₂ := b2e33 X0 X1
             grind)
          | exact superpose b2e33 b2e1087
          | (have j0 := b2e1087 X0 X1
             grind)
          | exact resolve b2e1087 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1087
        have b2e7540 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e906 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e906
          | exact resolve b2e906 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e906
        have b2e7791 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e7540 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7540
        have b2e7957 : ∀ X0 : G, y ≠ X0 ∨ y = (k (M.op y X0) y) ∨ (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e7791 (M.op y X0) y
             have i₂ := b2e24 X0
             grind)
          | exact superpose b2e24 b2e7791
          | (have j0 := b2e7791 (M.op y X0) y
             grind)
          | (have r₁ := b2e7791 (M.op y y) y
             have r₂ := b2e24 y
             grind)
          | exact resolve b2e7791 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e7791
        have b2e8086 : y = (k (M.op y y) y) ∨ y = (M.op y y) := by
          first
          | (have j0 := b2e7957 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7957
        have b2e8087 : y = (k (M.op y y) y) := by
          first
          | (have j1 := b2e38 y y
             grind)
          | (have r₁ := b2e8086
             have r₂ := b2e38 y x
             grind)
          | exact resolve b2e8086 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e8086
        have b2e9036 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e1100 (σ X0) X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1100
        have b2e9037 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e9036 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9036
        have b2e9067 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e9037 X0
             have i₂ := b2e18 X0 X0
             grind)
          | exact superpose b2e18 b2e9037
          | (have j0 := b2e9037 X0
             grind)
          | exact resolve b2e9037 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9037
        have b2e9130 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e9067 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e9067
          | exact resolve b2e9067 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e9178 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (k X0 X0)) X1)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (σ X0) (σ X0)
             have i₂ := b2e9067 X0
             grind)
          | exact superpose b2e9067 b2e12
          | (have j1 := b2e9067 X0
             grind)
          | exact resolve b2e12 b2e9067
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e9190 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e59 (σ X0) X1 (σ X0)
             have i₂ := b2e9067 X0
             grind)
          | exact superpose b2e9067 b2e59
          | (have j1 := b2e9067 X0
             grind)
          | exact resolve b2e59 b2e9067
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9067
        have b2e9226 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e9130 X0
             have i₂ := b2e34 X0 (τ X0)
             grind)
          | exact superpose b2e34 b2e9130
          | (have j0 := b2e9130 X0
             grind)
          | exact resolve b2e9130 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9130
        have b2e9236 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e9226 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e9226
          | (have j0 := b2e9226 X0
             grind)
          | exact resolve b2e9226 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9226
        have b2e9310 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e33 X0 (τ X0)
             have i₂ := b2e9236 (τ X0)
             grind)
          | exact superpose b2e9236 b2e33
          | (have j1 := b2e9236 (τ X0)
             grind)
          | exact resolve b2e33 b2e9236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9236
        have b2e9380 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e9310 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e9310
          | (have j0 := b2e9310 X0
             grind)
          | exact resolve b2e9310 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9310
        have b2e9469 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1071 (τ X0) (τ X1)
             have i₂ := b2e206 X1 X0
             grind)
          | exact superpose b2e206 b2e1071
          | (have j0 := b2e1071 (τ X0) (τ X1)
             grind)
          | exact resolve b2e1071 b2e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1071
        have b2e9544 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e9469 X0 X1
             have i₂ := b2e14 (k X0 X1)
             grind)
          | exact superpose b2e14 b2e9469
          | (have j0 := b2e9469 X0 X1
             grind)
          | exact resolve b2e9469 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9469
        have b2e9572 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e9544 X0 X1
             have i₂ := b2e14 X1
             grind)
          | exact superpose b2e14 b2e9544
          | (have j0 := b2e9544 X0 X1
             grind)
          | exact resolve b2e9544 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9544
        have b2e9592 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e9572 X0 X1
             have i₂ := b2e34 X0 (τ X1)
             grind)
          | exact superpose b2e34 b2e9572
          | (have j0 := b2e9572 X0 X1
             grind)
          | exact resolve b2e9572 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e9572
        have b2e9610 : ∀ X0 X1 : G, (k X1 X0) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e9592 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e9592
          | (have j0 := b2e9592 X0 X1
             grind)
          | exact resolve b2e9592 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9592
        have b2e9626 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e9610 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e9610
          | (have j0 := b2e9610 X0 X1
             grind)
          | exact resolve b2e9610 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9610
        have b2e9638 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) ≠ X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e9626 X0 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e9626
          | (have j0 := b2e9626 X0 X1
             grind)
          | exact resolve b2e9626 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9626
        have b2e9645 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e9638 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e9638
          | (have j0 := b2e9638 X0 X1
             grind)
          | exact resolve b2e9638 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9638
        have b2e9917 : y ≠ y ∨ (M.op (M.op y y) y) = (k y (M.op y y)) ∨ y = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e9645 (M.op y y) y
             have i₂ := b2e8087
             grind)
          | exact superpose b2e8087 b2e9645
          | (have j0 := b2e9645 (M.op y y) y
             grind)
          | (have r₁ := b2e9645 (M.op y y) y
             have r₂ := b2e8087
             grind)
          | exact resolve b2e9645 b2e8087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9645
        have b2e9946 : (M.op (M.op y y) y) = (k y (M.op y y)) ∨ y = (M.op (M.op y y) y) := by grind
        clear b2e9917
        have b2e9967 : (M.op y y) = (k y (M.op y y)) ∨ y = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e9946
             have i₂ := b2e27 y y
             grind)
          | exact superpose b2e27 b2e9946
          | exact resolve b2e9946 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9946
        have b2e9979 : y = (M.op y y) ∨ (M.op y y) = (k y (M.op y y)) := by
          first
          | (have i₁ := b2e9967
             have i₂ := b2e27 y y
             grind)
          | exact superpose b2e27 b2e9967
          | exact resolve b2e9967 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e9967
        have b2e9990 : (M.op y y) = (k y (M.op y y)) := by
          first
          | (have j1 := b2e31 y
             grind)
          | (have r₁ := b2e9979
             have r₂ := b2e31 y
             grind)
          | exact resolve b2e9979 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e9979
        have b2e10078 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e88 X1 X0
             have i₂ := b2e1102 X0 X1
             grind)
          | exact superpose b2e1102 b2e88
          | (have j1 := b2e1102 X0 X1
             grind)
          | exact resolve b2e88 b2e1102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1102
        have b2e13142 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e9380 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e9380
          | exact resolve b2e9380 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9380
        have b2e13219 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e13142 X0
             have i₂ := b2e18 X0 X0
             grind)
          | exact superpose b2e18 b2e13142
          | (have j0 := b2e13142 X0
             grind)
          | exact resolve b2e13142 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13142
        have b2e13526 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e79 X1 (k X0 X0)
             have i₂ := b2e13219 X0
             grind)
          | exact superpose b2e13219 b2e79
          | (have j1 := b2e13219 X0
             grind)
          | exact resolve b2e79 b2e13219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e13531 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e88 (k X0 X0) X1
             have i₂ := b2e13219 X0
             grind)
          | exact superpose b2e13219 b2e88
          | (have j1 := b2e13219 X0
             grind)
          | exact resolve b2e88 b2e13219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13219
        have b2e13586 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e13531 X0 X1
             have i₂ := b2e88 (M.op X0 X0) X1
             grind)
          | exact superpose b2e88 b2e13531
          | (have j0 := b2e13531 X0 X1
             grind)
          | exact resolve b2e13531 b2e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e88 b2e13531
        have b2e13591 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e13526 X0 X1
             have i₂ := b2e79 X1 (M.op X0 X0)
             grind)
          | exact superpose b2e79 b2e13526
          | (have j0 := b2e13526 X0 X1
             grind)
          | exact resolve b2e13526 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13526
        have b2e16909 : ∀ X0 X1 : G, (k (k X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e13586 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e13586
          | (have j0 := b2e13586 X1 X1
             grind)
          | exact resolve b2e13586 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13586
        have b2e17746 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e13591 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e13591
          | (have j0 := b2e13591 X1 X1
             grind)
          | exact resolve b2e13591 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13591
        have b2e31677 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op (k X0 (σ (τ X0))) X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e9178 (τ X0) X1
             have i₂ := b2e33 X0 (τ X0)
             grind)
          | exact superpose b2e33 b2e9178
          | (have j0 := b2e9178 (τ X0) X1
             grind)
          | exact resolve b2e9178 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9178
        have b2e31823 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e31677 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e31677
          | (have j0 := b2e31677 X0 X1
             grind)
          | exact resolve b2e31677 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31677
        have b2e31872 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) X1)) = X1 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e31823 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e31823
          | (have j0 := b2e31823 X0 X1
             grind)
          | exact resolve b2e31823 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31823
        have b2e32368 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (k X1 X1)) X0) ∨ (M.op X1 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31872 X1 (M.op (M.op X2 (k X1 X1)) X0)
             have i₂ := b2e12 X0 (k X1 X1) X2
             grind)
          | exact superpose b2e12 b2e31872
          | (have j0 := b2e31872 X1 X1
             grind)
          | exact resolve b2e31872 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32430 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (k X2 X2) X0) ∨ (M.op X2 X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e59 X2 X1 (M.op (k X2 X2) X0)
             have i₂ := b2e31872 X2 X0
             grind)
          | exact superpose b2e31872 b2e59
          | (have j1 := b2e31872 X2 X1
             grind)
          | exact resolve b2e59 b2e31872
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31872
        have b2e34001 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (k X0 X0) x
             have i₂ := b2e32368 X1 X0 x
             grind)
          | exact superpose b2e32368 b2e12
          | (have j1 := b2e32368 X0 X0 x
             grind)
          | exact resolve b2e12 b2e32368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32368
        have b2e42008 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (k (M.op y y) y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ (k (M.op y y) y)) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e1096 y (M.op y y)
             have i₂ := b2e9990
             grind)
          | exact superpose b2e9990 b2e1096
          | (have j0 := b2e1096 y (M.op y y)
             grind)
          | exact resolve b2e1096 b2e9990
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1096 b2e9990
        have b2e42064 : (σ (k (M.op y y) y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ (k (M.op y y) y)) = (M.op (σ y) (σ (M.op y y))) := by grind
        clear b2e42008
        have b2e42133 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ (k (M.op y y) y)) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e42064
             have i₂ := b2e8087
             grind)
          | exact superpose b2e8087 b2e42064
          | exact resolve b2e42064 b2e8087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42064
        have b2e42134 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ (k (M.op y y) y)) = (M.op (σ y) (σ (M.op y y))) := by grind
        clear b2e42133
        have b2e42206 : (σ y) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e42134
             have i₂ := b2e8087
             grind)
          | exact superpose b2e8087 b2e42134
          | exact resolve b2e42134 b2e8087
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8087 b2e42134
        have b2e119710 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e9190 (τ X0) X1
             have i₂ := b2e33 X0 (τ X0)
             grind)
          | exact superpose b2e33 b2e9190
          | (have j0 := b2e9190 (τ X0) X1
             grind)
          | exact resolve b2e9190 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e9190
        have b2e119824 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e119710 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e119710
          | (have j0 := b2e119710 X0 X1
             grind)
          | exact resolve b2e119710 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119710
        have b2e119840 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e119824 X0 X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e119824
          | (have j0 := b2e119824 X0 X1
             grind)
          | exact resolve b2e119824 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119824
        have b2e120400 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e32430 (k X0 X0) x X0
             have i₂ := b2e119840 X0 x
             grind)
          | exact superpose b2e119840 b2e32430
          | (have j0 := b2e32430 X0 x X0
             have j1 := b2e119840 X0 x
             grind)
          | exact resolve b2e32430 b2e119840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32430
        have b2e120524 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e120400 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120400
        have b2e124908 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e34001 (k X0 X0) (k X0 X0)
             have i₂ := b2e120524 X0
             grind)
          | exact superpose b2e120524 b2e34001
          | (have j0 := b2e34001 X0 x
             have j1 := b2e120524 X0
             grind)
          | exact resolve b2e34001 b2e120524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34001
        have b2e124919 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e119840 (k X0 X0) (k X0 X0)
             have i₂ := b2e120524 X0
             grind)
          | exact superpose b2e120524 b2e119840
          | (have j0 := b2e119840 X0 x
             have j1 := b2e120524 X0
             grind)
          | exact resolve b2e119840 b2e120524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119840
        have b2e124972 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e124919 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e124919 x
             have r₂ := b2e15 x x
             grind)
          | exact resolve b2e124919 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124919
        have b2e124976 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X0) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e124908 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e124908 x
             have r₂ := b2e15 x x
             grind)
          | exact resolve b2e124908 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124908
        have b2e143319 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e124972 x
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e124972
          | (have j1 := b2e17 X0 X0
             grind)
          | exact resolve b2e124972 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124972
        have b2e143406 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e143319 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e143319
        have b2e144573 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (k X0 X0) X2) ∨ (k X0 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e98 X2 X1 X0 (k (k X0 X0) (k X0 X0))
             have i₂ := b2e124976 X0
             grind)
          | exact superpose b2e124976 b2e98
          | (have j1 := b2e124976 X0
             grind)
          | exact resolve b2e98 b2e124976
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98 b2e124976
        have b2e149784 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e144573 X0 X1 (k X0 X0)
             have i₂ := b2e120524 X0
             grind)
          | exact superpose b2e120524 b2e144573
          | (have j0 := b2e144573 X0 X1 x
             have j1 := b2e120524 X0
             grind)
          | exact resolve b2e144573 b2e120524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120524
        have b2e150457 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e149784 X0 X1
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e149784 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | exact resolve b2e149784 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e149784
        have b2e151194 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 (k X0 X0) X0 x
             have i₂ := b2e150457 X0 x
             grind)
          | exact superpose b2e150457 b2e12
          | (have j1 := b2e150457 X0 x
             grind)
          | exact resolve b2e12 b2e150457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150457
        have b2e151914 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e151194 (τ X0)
             have i₂ := b2e206 X0 X0
             grind)
          | exact superpose b2e206 b2e151194
          | exact resolve b2e151194 b2e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e165264 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e59 X0 X1 (k (M.op X0 X0) (M.op X0 X0))
             have i₂ := b2e143406 X0
             grind)
          | exact superpose b2e143406 b2e59
          | (have j1 := b2e143406 X0
             grind)
          | exact resolve b2e59 b2e143406
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e143406
        have b2e165338 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e165264 X0 x
             have i₂ := b2e59 X0 x X0
             grind)
          | exact superpose b2e59 b2e165264
          | (have j0 := b2e165264 X0 x
             grind)
          | exact resolve b2e165264 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e165264
        have b2e166219 : ∀ X0 : G, (τ X0) = (k (τ (k X0 X0)) (τ (k X0 X0))) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e165338 (τ X0)
             have i₂ := b2e151914 X0
             grind)
          | exact superpose b2e151914 b2e165338
          | (have j1 := b2e151914 X0
             grind)
          | exact resolve b2e165338 b2e151914
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e151914 b2e165338
        have b2e166359 : ∀ X0 : G, (τ X0) = (k (τ (k X0 X0)) (τ (k X0 X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e166219 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166219
        have b2e166367 : ∀ X0 : G, (τ X0) = (τ (k (k X0 X0) (k X0 X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e166359 X0
             have i₂ := b2e206 (k X0 X0) (k X0 X0)
             grind)
          | exact superpose b2e206 b2e166359
          | (have j0 := b2e166359 X0
             grind)
          | exact resolve b2e166359 b2e206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e206 b2e166359
        have b2e193786 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e238 X0 (σ X0) (k (σ X0) (σ X0))
             have i₂ := b2e166367 (σ X0)
             grind)
          | exact superpose b2e166367 b2e238
          | (have j1 := b2e166367 (σ X0)
             grind)
          | exact resolve b2e238 b2e166367
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238 b2e166367
        have b2e193831 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e193786 X0
             have i₂ := b2e79 (σ X0) X0
             grind)
          | exact superpose b2e79 b2e193786
          | (have j0 := b2e193786 X0
             grind)
          | exact resolve b2e193786 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193786
        have b2e193842 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e193831 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e193831
          | (have j0 := b2e193831 X0
             grind)
          | exact resolve b2e193831 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193831
        have b2e193851 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e193842 X0
             have i₂ := b2e79 (σ X0) X0
             grind)
          | exact superpose b2e79 b2e193842
          | (have j0 := b2e193842 X0
             grind)
          | exact resolve b2e193842 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193842
        have b2e193860 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e193851 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e193851
          | (have j0 := b2e193851 X0
             grind)
          | exact resolve b2e193851 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193851
        have b2e193902 : ∀ X0 : G, (k (M.op X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e193860 X0
             have i₂ := b2e16909 (k X0 X0) X0
             grind)
          | exact superpose b2e16909 b2e193860
          | (have j0 := b2e193860 X0
             have j1 := b2e16909 X0 X0
             grind)
          | exact resolve b2e193860 b2e16909
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16909
        have b2e194104 : ∀ X0 : G, (k (M.op X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e193902 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e193902 x
             have r₂ := b2e15 x x
             grind)
          | exact resolve b2e193902 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193902
        have b2e195154 : ∀ X0 : G, (k X0 X0) = (k (M.op (k X0 X0) (k X0 X0)) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e194104 (k X0 X0)
             have i₂ := b2e193860 X0
             grind)
          | exact superpose b2e193860 b2e194104
          | (have j0 := b2e194104 X0
             have j1 := b2e193860 X0
             grind)
          | exact resolve b2e194104 b2e193860
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e194104
        have b2e195205 : ∀ X0 : G, (k X0 X0) = (k (M.op (k X0 X0) (k X0 X0)) X0) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e195154 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e195154
        have b2e203187 : ∀ X0 : G, (τ (σ x)) = (k y (τ (M.op X0 (σ y)))) ∨ (σ x) = (k (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e10078 (M.op X0 (σ y)) y
             have i₂ := b2e313 X0
             grind)
          | exact superpose b2e313 b2e10078
          | exact resolve b2e10078 b2e313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10078
        have b2e203196 : ∀ X0 : G, (τ (σ x)) = (k y (τ (M.op X0 (σ y)))) ∨ (σ x) = (k (M.op X0 (σ y)) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e203187 X0
             grind)
          | (have r₁ := b2e203187 X0
             have r₂ := b2e303
             grind)
          | exact resolve b2e203187 b2e303
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e203187
        have b2e203201 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ y)) (σ y)) ∨ x = (k y (τ (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b2e203196 X0
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e203196
          | (have j0 := b2e203196 X0
             grind)
          | exact resolve b2e203196 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e203196
        have b2e215424 : ∀ X0 X1 : G, (k X1 X1) = (k (M.op (M.op X0 X1) (k X1 X1)) X1) ∨ (k X1 X1) = X1 ∨ (k X1 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e195205 X1
             have i₂ := b2e144573 X1 X0 (k X1 X1)
             grind)
          | exact superpose b2e144573 b2e195205
          | (have j0 := b2e195205 X1
             have j1 := b2e144573 X1 X1 x
             grind)
          | exact resolve b2e195205 b2e144573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e144573 b2e195205
        have b2e215428 : ∀ X0 X1 : G, (k X1 X1) = (k (M.op (M.op X0 X1) (k X1 X1)) X1) ∨ (k X1 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e215424 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e215424
        have b2e221147 : ∀ X0 X1 : G, (k (M.op (M.op X1 (k X0 X0)) X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e215428 X0 (k X0 X0)
             have i₂ := b2e193860 X0
             grind)
          | exact superpose b2e193860 b2e215428
          | (have j0 := b2e215428 X0 X0
             have j1 := b2e193860 X0
             grind)
          | exact resolve b2e215428 b2e193860
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193860 b2e215428
        have b2e221170 : ∀ X0 X1 : G, (k (M.op (M.op X1 (k X0 X0)) X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e221147 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e221147
        have b2e223403 : ∀ X0 X1 : G, (k (M.op (M.op X1 (k X0 X0)) X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e17746 (M.op (M.op X1 (k X0 X0)) X0) X0
             have i₂ := b2e221170 X0 X1
             grind)
          | exact superpose b2e221170 b2e17746
          | (have j0 := b2e17746 X0 X0
             have j1 := b2e221170 X0 X1
             grind)
          | exact resolve b2e17746 b2e221170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17746 b2e221170
        have b2e223442 : ∀ X0 X1 : G, (k (M.op (M.op X1 (k X0 X0)) X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e223403 X0 X1
             have j1 := b2e591 X0
             grind)
          | (have r₁ := b2e223403 X0 X1
             have r₂ := b2e591 X0
             grind)
          | exact resolve b2e223403 b2e591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e591 b2e223403
        have b2e228934 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op X0 (σ y))) y) ∨ x = (k y (τ (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b2e79 (M.op X0 (σ y)) y
             have i₂ := b2e203201 X0
             grind)
          | exact superpose b2e203201 b2e79
          | (have j1 := b2e203201 X0
             grind)
          | exact resolve b2e79 b2e203201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79 b2e203201
        have b2e228939 : ∀ X0 : G, x = (k (τ (M.op X0 (σ y))) y) ∨ x = (k y (τ (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b2e228934 X0
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e228934
          | (have j0 := b2e228934 X0
             grind)
          | exact resolve b2e228934 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e228934
        have b2e237461 : x = (k (τ (σ y)) y) ∨ x = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e228939 (σ (M.op y y))
             have i₂ := b2e42206
             grind)
          | exact superpose b2e42206 b2e228939
          | exact resolve b2e228939 b2e42206
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42206 b2e228939
        have b2e237503 : x = (k y y) ∨ x = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e237461
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e237461
          | exact resolve b2e237461 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e237461
        have b2e237507 : x = (k y y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ y) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e237503
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e237503
          | exact resolve b2e237503 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e237503
        have b2e237508 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ x = (k y y) := by grind
        clear b2e237507
        have b2e237531 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (σ (M.op y y)) ∨ x = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e59 (σ y) X0 (σ (M.op y y))
             have i₂ := b2e237508
             grind)
          | exact superpose b2e237508 b2e59
          | exact resolve b2e59 b2e237508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59 b2e237508
        have b2e237553 : (σ x) = (σ (M.op y y)) ∨ x = (k y y) := by
          first
          | (have i₁ := b2e237531 x
             have i₂ := b2e313 x
             grind)
          | exact superpose b2e313 b2e237531
          | exact resolve b2e237531 b2e313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e313 b2e237531
        have b2e237568 : (M.op y y) = (τ (σ x)) ∨ x = (k y y) := by
          first
          | (have i₁ := b2e13 (M.op y y)
             have i₂ := b2e237553
             grind)
          | exact superpose b2e237553 b2e13
          | exact resolve b2e13 b2e237553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e237553
        have b2e237653 : x = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b2e237568
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e237568
          | exact resolve b2e237568 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e237568
        have b2e237936 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b2e151194 y
             have i₂ := b2e237653
             grind)
          | exact superpose b2e237653 b2e151194
          | exact resolve b2e151194 b2e237653
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e151194 b2e237653
        have b2e238124 : x = (M.op y y) ∨ x = y := by grind
        clear b2e237936
        have b2e238335 : ∀ X0 : G, y = (k (M.op (M.op X0 (k y y)) y) x) ∨ x = y ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e223442 y x
             have i₂ := b2e238124
             grind)
          | exact superpose b2e238124 b2e223442
          | exact resolve b2e223442 b2e238124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e223442 b2e238124
        have b2e238418 : ∀ X0 : G, y = (k (M.op (M.op X0 (k y y)) y) x) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e238335 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238335
        have b2e238473 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e238418 x
             have i₂ := b2e739 (M.op x (k y y))
             grind)
          | exact superpose b2e739 b2e238418
          | exact resolve b2e238418 b2e739
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e739 b2e238418
        have b2e238474 : x = y := by grind
        clear b2e238473
        have b2e238505 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e303
             have i₂ := b2e238474
             grind)
          | exact superpose b2e238474 b2e303
          | exact resolve b2e303 b2e238474
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e303 b2e238474
        have b2e238852 : False := by grind
        exact b2e238852
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e31 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e29
        have b3e33 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e31
          | exact resolve b3e31 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e42 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
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
        have b3e43 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
        clear b3e42
        have b3e45 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e43
             have r₂ := b3e20
             grind)
          | exact resolve b3e43 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e67 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b3e33
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e33
          | exact resolve b3e33 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e45
        have b3e69 : False := by grind
        exact b3e69
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x y) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
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
          have b4e48 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b4e47
          have b4e49 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b4e44
          have b4e50 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e48
               have r₂ := b4e21
               grind)
            | exact resolve b4e48 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e51 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e49
               have r₂ := b4e23
               grind)
            | exact resolve b4e49 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e52 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e51
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e51
            | exact resolve b4e51 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e53 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e52
               have i₂ := b4e50
               grind)
            | exact superpose b4e50 b4e52
            | exact resolve b4e52 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50 b4e52
          have b4e54 : False := by grind
          exact b4e54
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : x ≠ x ∨ x = (k y x) := by
            first
            | (have i₁ := b5e16 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y x
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : x = (k y x) := by grind
          clear b5e28
          have b5e47 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
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
          have b5e48 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b5e47
          have b5e49 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e252 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e53 x y
               grind)
            | exact superpose b5e53 b5e24
            | (have j1 := b5e53 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e53 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e53 y x
               grind)
            | exact resolve b5e24 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e269 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e252
          have b5e274 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e269
               have r₂ := b5e23
               grind)
            | exact resolve b5e269 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e269
          have b5e280 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e274
               have i₂ := b5e30
               grind)
            | exact superpose b5e30 b5e274
            | exact resolve b5e274 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e274
          have b5e314 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e280
               grind)
            | exact superpose b5e280 b5e23
            | exact resolve b5e23 b5e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e315 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ y) (σ x)
               have i₂ := b5e280
               grind)
            | exact superpose b5e280 b5e13
            | exact resolve b5e13 b5e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e466 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e315 (σ y)
               have i₂ := b5e280
               grind)
            | exact superpose b5e280 b5e315
            | exact resolve b5e315 b5e280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e280 b5e315
          have b5e492 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e53 y x
               have i₂ := b5e466
               grind)
            | exact superpose b5e466 b5e53
            | (have j0 := b5e53 y x
               grind)
            | exact resolve b5e53 b5e466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e466
          have b5e510 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e492
               have r₂ := b5e23
               grind)
            | exact resolve b5e492 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e492
          have b5e516 : (σ y) = (σ (k x y)) := by
            first
            | (have r₁ := b5e510
               have r₂ := b5e314
               grind)
            | exact resolve b5e510 b5e314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e314 b5e510
          have b5e520 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b5e516
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e516
            | exact resolve b5e516 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e516
          have b5e547 : (M.op x y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (M.op x y)
               have i₂ := b5e520
               grind)
            | exact superpose b5e520 b5e14
            | exact resolve b5e14 b5e520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e520
          have b5e560 : y = (M.op x y) := by
            first
            | (have i₁ := b5e547
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e547
            | exact resolve b5e547 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e547
          have b5e561 : False := by grind
          exact b5e561
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X3 (M.op (M.op X1 X2) X0) X2
             have i₂ := b6e12 X0 X2 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X3 (M.op X2 X1)) X0) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op (M.op X3 (M.op X2 X1)) X0) X1 X2
             have i₂ := b6e12 X0 (M.op X2 X1) X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e28 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) ≠ X0 ∨ (M.op (M.op X2 X1) X0) = (k X1 (M.op (M.op X2 X1) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 (M.op (M.op X2 X1) X0)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X2 X1) X0
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e27
        have b6e30 : (σ y) = (σ (k x y)) := by
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
        have b6e31 : (k x y) = (τ (σ y)) := by
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
        have b6e32 : y = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e35 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e39 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
        clear b6e39
        have b6e42 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e41
          | exact resolve b6e41 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e49 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
        have b6e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : y = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e49
             have r₂ := b6e21
             grind)
          | exact resolve b6e49 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e56 : y = (M.op y x) := by
          first
          | (have r₁ := b6e53
             have r₂ := b6e20
             grind)
          | exact resolve b6e53 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e58 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e21
          | exact resolve b6e21 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e61 : ∀ X0 : G, (M.op x (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e12
          | exact resolve b6e12 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e33 X0 X1
             grind)
          | exact superpose b6e33 b6e13
          | exact resolve b6e13 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e69 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e35 X0 X1
             have i₂ := b6e17 X1 (τ X0)
             grind)
          | exact superpose b6e17 b6e35
          | (have j1 := b6e17 X1 (τ X0)
             grind)
          | exact resolve b6e35 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e97 : ∀ X0 X1 X4 : G, (M.op (M.op X1 X0) (M.op X0 X4)) = X4 := by
          intro X0 X1 X4
          first
          | (have i₁ := b6e12 X4 (M.op X1 X0) (M.op (M.op x x) X1)
             have i₂ := b6e25 X1 x x X0
             grind)
          | exact superpose b6e25 b6e12
          | exact resolve b6e12 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e98 : x = (M.op x y) := by
          first
          | (have i₁ := b6e61 x
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e61
          | exact resolve b6e61 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e99 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e61 (M.op (M.op X1 y) X0)
             have i₂ := b6e12 X0 y X1
             grind)
          | exact superpose b6e12 b6e61
          | exact resolve b6e61 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e100 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op (M.op X1 X2) x) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e25 x X1 X2 (M.op y X0)
             have i₂ := b6e61 X0
             grind)
          | exact superpose b6e61 b6e25
          | exact resolve b6e25 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X3 X0) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e26 X2 (M.op X1 X0) (M.op (M.op x x) X1) X3
             have i₂ := b6e25 X1 x x X0
             grind)
          | exact superpose b6e25 b6e26
          | exact resolve b6e26 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e110 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e26 X1 (M.op y X0) x X2
             have i₂ := b6e61 X0
             grind)
          | exact superpose b6e61 b6e26
          | exact resolve b6e26 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e135 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 y x
             have i₂ := b6e98
             grind)
          | exact superpose b6e98 b6e12
          | exact resolve b6e12 b6e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e145 : (σ x) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b6e42
        have b6e157 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k (M.op X3 X0) (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e28 X0 (M.op x X1) X3
             have i₂ := b6e26 X0 X1 x X3
             grind)
          | exact superpose b6e26 b6e28
          | exact resolve b6e28 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26 b6e28
        have b6e203 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (σ X1) (σ X0)
             have i₂ := b6e51 X0 X1
             grind)
          | exact superpose b6e51 b6e15
          | (have j0 := b6e15 (σ X1) (σ X0)
             have j1 := b6e51 X0 X1
             grind)
          | (have r₁ := b6e15 (σ X1) (σ X0)
             have r₂ := b6e51 X0 X1
             grind)
          | (have r₁ := b6e15 (σ X0) (σ X1)
             have r₂ := b6e51 X0 X1
             grind)
          | exact resolve b6e15 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e206 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (M.op X1 X2) (σ X3)) (σ X0)) ∨ (M.op (σ X0) (σ X3)) = (σ (k X3 X0)) ∨ (σ X3) = (M.op (σ X0) (σ X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e25 (σ X3) X1 X2 (σ X0)
             have i₂ := b6e51 X0 X3
             grind)
          | exact superpose b6e51 b6e25
          | (have j1 := b6e51 X0 X3
             grind)
          | exact resolve b6e25 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e209 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e51 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e211 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e209 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e209
        have b6e214 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e203 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203
        have b6e217 : ∀ X0 X3 : G, (σ X0) = (M.op (M.op y (σ X3)) (σ X0)) ∨ (M.op (σ X0) (σ X3)) = (σ (k X3 X0)) ∨ (σ X3) = (M.op (σ X0) (σ X3)) := by
          intro X0 X3
          first
          | (have i₁ := b6e206 X0 x x X3
             have i₂ := b6e110 (σ X3) (σ X0) (M.op x x)
             grind)
          | exact superpose b6e110 b6e206
          | (have j0 := b6e206 X0 x x X3
             grind)
          | exact resolve b6e206 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e206
        have b6e219 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e214 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e214
          | (have j0 := b6e214 X0 X1
             grind)
          | exact resolve b6e214 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e214
        have b6e279 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ X2)) (σ X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (σ X2) = (M.op (σ X0) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e97 (σ X2) X1 (σ X0)
             have i₂ := b6e51 X0 X2
             grind)
          | exact superpose b6e51 b6e97
          | (have j1 := b6e51 X0 X2
             grind)
          | exact resolve b6e97 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e97
        have b6e693 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k (M.op X3 X1) X2) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e15 (M.op X3 X1) X2
             have i₂ := b6e106 X1 X3 X2 X0
             grind)
          | (have i₁ := b6e15 (M.op X3 X1) X2
             have i₂ := b6e106 X1 X0 X2 X3
             grind)
          | exact superpose b6e106 b6e15
          | (have j0 := b6e15 (M.op X0 X1) X2
             grind)
          | exact resolve b6e15 b6e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1494 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e145
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e145
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e145 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145
        have b6e1495 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e1494
             have r₂ := b6e20
             grind)
          | exact resolve b6e1494 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1494
        have b6e1496 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b6e1495
             have r₂ := b6e21
             grind)
          | exact resolve b6e1495 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1495
        have b6e1497 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e1496
             have i₂ := b6e98
             grind)
          | exact superpose b6e98 b6e1496
          | exact resolve b6e1496 b6e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e98 b6e1496
        have b6e1498 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b6e1497
        have b6e1543 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e211 (τ X0)
             have i₂ := b6e35 X0 (τ X0)
             grind)
          | exact superpose b6e35 b6e211
          | (have j0 := b6e211 (τ X0)
             grind)
          | exact resolve b6e211 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e211
        have b6e1545 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b6e1543 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1543
          | (have j0 := b6e1543 X0
             grind)
          | exact resolve b6e1543 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1543
        have b6e1548 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e1545 X0
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e1545
          | (have j0 := b6e1545 X0
             grind)
          | exact resolve b6e1545 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1545
        have b6e1606 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (M.op X0 (σ y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e157 (σ y) (σ x) x
             have i₂ := b6e1498
             grind)
          | exact superpose b6e1498 b6e157
          | (have r₁ := b6e157 (σ y) (σ x) x
             have r₂ := b6e1498
             grind)
          | exact resolve b6e157 b6e1498
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e157 b6e1498
        have b6e1616 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ y)) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e1606 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1606
        have b6e1752 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op X0 (σ y))) x) := by
          intro X0
          first
          | (have i₁ := b6e67 (M.op X0 (σ y)) x
             have i₂ := b6e1616 X0
             grind)
          | exact superpose b6e1616 b6e67
          | exact resolve b6e67 b6e1616
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1616
        have b6e1755 : ∀ X0 : G, x = (k (τ (M.op X0 (σ y))) x) := by
          intro X0
          first
          | (have i₁ := b6e1752 X0
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1752
          | exact resolve b6e1752 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1752
        have b6e2134 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ (M.op (M.op X1 (τ X2)) X0)) X2) ∨ (M.op (M.op X1 (τ X2)) X0) = X0 ∨ (τ X2) = (M.op (M.op (M.op X1 (τ X2)) X0) (τ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e69 X0 (M.op (M.op X2 (τ X0)) X0)
             have i₂ := b6e12 X0 (τ X0) X2
             grind)
          | exact superpose b6e12 b6e69
          | (have j0 := b6e69 X2 (M.op (M.op X1 (τ X2)) X0)
             grind)
          | exact resolve b6e69 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e2163 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ (M.op (M.op X1 (τ X2)) X0)) X2) ∨ (τ X2) = (M.op (M.op y X0) (τ X2)) ∨ (M.op (M.op X1 (τ X2)) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e2134 X0 X1 X2
             have i₂ := b6e110 X0 (τ X2) (M.op X1 (τ X2))
             grind)
          | exact superpose b6e110 b6e2134
          | (have j0 := b6e2134 X0 X1 X2
             grind)
          | exact resolve b6e2134 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110 b6e2134
        have b6e2346 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k (τ X0) X1)) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e219 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e219
          | (have j0 := b6e219 X1 (τ X0)
             grind)
          | exact resolve b6e219 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e219
        have b6e2414 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (k (τ X0) X1)) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e2346 X0 X1
             have i₂ := b6e33 X0 X1
             grind)
          | exact superpose b6e33 b6e2346
          | (have j0 := b6e2346 X0 X1
             grind)
          | exact resolve b6e2346 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2346
        have b6e2429 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (k X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e2414 X0 X1
             have i₂ := b6e33 X0 X1
             grind)
          | exact superpose b6e33 b6e2414
          | (have j0 := b6e2414 X0 X1
             grind)
          | exact resolve b6e2414 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33 b6e2414
        have b6e2963 : ∀ X0 X1 : G, (M.op (M.op y (σ X1)) X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e217 (τ X0) x
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e217
          | exact resolve b6e217 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e217
        have b6e3049 : ∀ X0 X1 : G, (M.op (M.op y (σ X1)) X0) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e2963 X0 X1
             have i₂ := b6e35 X0 X1
             grind)
          | exact superpose b6e35 b6e2963
          | (have j0 := b6e2963 X0 X1
             grind)
          | exact resolve b6e2963 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e2963
        have b6e13212 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e2429 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e2429
          | exact resolve b6e2429 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2429
        have b6e13526 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e13212 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13212
        have b6e13697 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) X0) X1) = X1 ∨ (M.op (M.op X2 X1) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e13526 (M.op (M.op X2 X1) X0) X1
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e13526
          | (have j0 := b6e13526 (M.op (M.op X2 X1) X0) X1
             grind)
          | (have r₁ := b6e13526 (M.op (M.op X2 X0) X0) X0
             have r₂ := b6e12 X0 X0 X2
             grind)
          | exact resolve b6e13526 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13526
        have b6e16642 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e3049 X0 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e3049
          | exact resolve b6e3049 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3049
        have b6e17224 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e106 X2 X1 X0 y
             have i₂ := b6e16642 X2 X0
             grind)
          | exact superpose b6e16642 b6e106
          | (have j1 := b6e16642 X2 X0
             grind)
          | exact resolve b6e106 b6e16642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106 b6e16642
        have b6e42019 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X1 (τ (σ X2))) X0))) X2) ∨ (τ (σ X2)) = (M.op (M.op y X0) (τ (σ X2))) ∨ (M.op (M.op X1 (τ (σ X2))) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e67 (σ (M.op (M.op X1 (τ (σ X2))) X0)) X2
             have i₂ := b6e2163 X0 X1 (σ X2)
             grind)
          | exact superpose b6e2163 b6e67
          | (have j1 := b6e2163 X0 X1 (σ X2)
             grind)
          | exact resolve b6e67 b6e2163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67 b6e2163
        have b6e42100 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op (M.op X1 (τ (σ X2))) X0) X2) ∨ (τ (σ X2)) = (M.op (M.op y X0) (τ (σ X2))) ∨ (M.op (M.op X1 (τ (σ X2))) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e42019 X0 X1 X2
             have i₂ := b6e13 (M.op (M.op X1 (τ (σ X2))) X0)
             grind)
          | exact superpose b6e13 b6e42019
          | (have j0 := b6e42019 X0 X1 X2
             grind)
          | exact resolve b6e42019 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42019
        have b6e42150 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op (M.op X1 X2) X0) X2) ∨ (τ (σ X2)) = (M.op (M.op y X0) (τ (σ X2))) ∨ (M.op (M.op X1 (τ (σ X2))) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e42100 X0 X1 X2
             have i₂ := b6e13 X2
             grind)
          | exact superpose b6e13 b6e42100
          | (have j0 := b6e42100 X0 X1 X2
             grind)
          | exact resolve b6e42100 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42100
        have b6e42181 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) X0) X2) = X0 ∨ (τ (σ X2)) = (M.op (M.op y X0) (τ (σ X2))) ∨ (M.op (M.op X1 (τ (σ X2))) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e42150 X0 X1 X2
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e42150
          | (have j0 := b6e42150 X0 X1 X2
             grind)
          | exact resolve b6e42150 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42150
        have b6e42211 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = X2 ∨ (k (M.op (M.op X1 X2) X0) X2) = X0 ∨ (M.op (M.op X1 (τ (σ X2))) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e42181 X0 X1 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e42181
          | (have j0 := b6e42181 X0 X1 X2
             grind)
          | exact resolve b6e42181 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42181
        have b6e42229 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X2) X0) X2) = X0 ∨ (M.op (M.op y X0) X2) = X2 ∨ (M.op (M.op X1 X2) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e42211 X0 X1 X2
             have i₂ := b6e13 X2
             grind)
          | exact superpose b6e13 b6e42211
          | (have j0 := b6e42211 X0 X1 X2
             grind)
          | exact resolve b6e42211 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42211
        have b6e76765 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X1) = X1 ∨ (M.op (M.op X0 X1) X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e13697 X1 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13697
        have b6e76766 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e76765 X0 X1
             have j1 := b6e693 X0 X1 X1 (M.op X0 X1)
             grind)
          | (have r₁ := b6e76765 X0 x
             have r₂ := b6e693 X0 x x x
             grind)
          | exact resolve b6e76765 b6e693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e693 b6e76765
        have b6e77256 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e76766 x X0
             have i₂ := b6e17224 X0 x X0
             grind)
          | exact superpose b6e17224 b6e76766
          | (have j1 := b6e17224 X0 x X0
             grind)
          | exact resolve b6e76766 b6e17224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17224
        have b6e77284 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e76766 x (σ X0)
             have i₂ := b6e279 X0 x X0
             grind)
          | exact superpose b6e279 b6e76766
          | (have j1 := b6e279 X0 x X0
             grind)
          | exact resolve b6e76766 b6e279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e279 b6e76766
        have b6e77427 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have j0 := b6e77284 X0
             have j1 := b6e15 (σ X0) (σ X0)
             grind)
          | (have r₁ := b6e77284 X0
             have r₂ := b6e15 (σ X0) (σ X0)
             grind)
          | exact resolve b6e77284 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77284
        have b6e77430 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e77256 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e77256 x
             have r₂ := b6e15 x x
             grind)
          | exact resolve b6e77256 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77256
        have b6e77464 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e77427 X0
             have i₂ := b6e18 X0 X0
             grind)
          | exact superpose b6e18 b6e77427
          | (have j0 := b6e77427 X0
             grind)
          | exact resolve b6e77427 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77427
        have b6e90384 : x = (k (τ (σ (k y y))) x) ∨ (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e1755 (σ y)
             have i₂ := b6e77464 y
             grind)
          | exact superpose b6e77464 b6e1755
          | (have j1 := b6e77464 y
             grind)
          | exact resolve b6e1755 b6e77464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1755 b6e77464
        have b6e90460 : x = (k (k y y) x) ∨ (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e90384
             have i₂ := b6e13 (k y y)
             grind)
          | exact superpose b6e13 b6e90384
          | exact resolve b6e90384 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90384
        have b6e90804 : x = (k (M.op y y) x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k y y) := by
          first
          | (have i₁ := b6e90460
             have i₂ := b6e77430 y
             grind)
          | exact superpose b6e77430 b6e90460
          | (have j1 := b6e77430 y
             grind)
          | exact resolve b6e90460 b6e77430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77430 b6e90460
        have b6e293656 : ∀ X0 : G, (k (M.op y X0) x) = X0 ∨ x = (M.op (M.op y X0) x) ∨ (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e42229 X0 (M.op x x) x
             have i₂ := b6e100 X0 x x
             grind)
          | exact superpose b6e100 b6e42229
          | (have j0 := b6e42229 X0 x x
             grind)
          | exact resolve b6e42229 b6e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e100 b6e42229
        have b6e306516 : x = y ∨ x = (M.op (M.op y y) x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k y y) := by
          first
          | (have i₁ := b6e293656 y
             have i₂ := b6e90804
             grind)
          | exact superpose b6e90804 b6e293656
          | (have j0 := b6e293656 y
             grind)
          | exact resolve b6e293656 b6e90804
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90804 b6e293656
        have b6e306517 : x = y ∨ x = (M.op (M.op y y) x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have j1 := b6e1548 y
             grind)
          | (have r₁ := b6e306516
             have r₂ := b6e1548 y
             grind)
          | exact resolve b6e306516 b6e1548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1548 b6e306516
        have b6e306519 : x = (M.op (M.op y y) x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have r₁ := b6e306517
             have r₂ := b6e58
             grind)
          | exact resolve b6e306517 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58 b6e306517
        have b6e306521 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e306519
             have i₂ := b6e99 x y
             grind)
          | exact superpose b6e99 b6e306519
          | exact resolve b6e306519 b6e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99 b6e306519
        have b6e306604 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e306521
             grind)
          | exact superpose b6e306521 b6e13
          | exact resolve b6e13 b6e306521
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e306521
        have b6e306641 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e306604
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e306604
          | exact resolve b6e306604 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e306604
        have b6e306642 : x = (M.op x x) ∨ y = (M.op y y) := by grind
        clear b6e306641
        have b6e306716 : x = (M.op y x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e135 x
             have i₂ := b6e306642
             grind)
          | exact superpose b6e306642 b6e135
          | exact resolve b6e135 b6e306642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e135 b6e306642
        have b6e306870 : y = (M.op y y) := by
          first
          | (have r₁ := b6e306716
             have r₂ := b6e21
             grind)
          | exact resolve b6e306716 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e306716
        have b6e306942 : y = (M.op x y) := by
          first
          | (have i₁ := b6e61 y
             have i₂ := b6e306870
             grind)
          | exact superpose b6e306870 b6e61
          | exact resolve b6e61 b6e306870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e306870
        have b6e307116 : False := by grind
        exact b6e307116
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) (σ x)
               grind)
            | (have r₁ := b7e16 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : (σ x) = (k (σ y) (σ x)) := by grind
          clear b7e28
          have b7e31 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e30
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e30
            | exact resolve b7e30 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e32 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e31
               grind)
            | exact superpose b7e31 b7e14
            | exact resolve b7e14 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e33 : x = (k y x) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e32
            | exact resolve b7e32 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e47 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
          have b7e57 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e60 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e21
               grind)
            | exact resolve b7e57 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e63 : x = (M.op x y) := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e68 : ∀ X0 : G, (M.op y (M.op x X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e13
            | exact resolve b7e13 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : (σ y) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e23
            | exact resolve b7e23 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e111 : (σ y) ≠ (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e80
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e80
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e80 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e112 : (σ y) ≠ (σ (M.op y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e111
               have r₂ := b7e22
               grind)
            | exact resolve b7e111 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e113 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e112
               have r₂ := b7e21
               grind)
            | exact resolve b7e112 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112
          have b7e232 : y = (M.op y x) := by
            first
            | (have i₁ := b7e68 y
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e68
            | exact resolve b7e68 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e68
          have b7e282 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b7e113
               have i₂ := b7e232
               grind)
            | exact superpose b7e232 b7e113
            | exact resolve b7e113 b7e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113 b7e232
          have b7e294 : False := by grind
          exact b7e294
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e44 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e158 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e44 x y
               grind)
            | exact superpose b8e44 b8e24
            | (have j1 := b8e44 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e44 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e44 y x
               grind)
            | exact resolve b8e24 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e174 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e158
          have b8e179 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e174
               have r₂ := b8e23
               grind)
            | exact resolve b8e174 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e186 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e179
               grind)
            | exact superpose b8e179 b8e20
            | exact resolve b8e20 b8e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179
          have b8e306 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e186
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e186
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e186 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e307 : y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b8e306
          have b8e308 : x = (M.op y x) := by
            first
            | (have r₁ := b8e307
               have r₂ := b8e21
               grind)
            | exact resolve b8e307 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e307
          have b8e309 : False := by grind
          exact b8e309

/-- `Equation138`: `x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation138 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law138 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law138.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X0 X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op x X0) x
           have i₂ := b0e21 X0
           grind)
        | exact superpose b0e21 b0e11
        | exact resolve b0e11 b0e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e20
           grind)
        | exact resolve b0e15 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e19
           grind)
        | exact resolve b0e15 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
      clear b0e43
      have b0e45 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
      clear b0e40
      have b0e46 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e45
        | exact resolve b0e45 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X0 X1
           have i₂ := b0e16 (σ X0) (σ X1)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 (M.op X1 X0) (M.op x X1)
           have i₂ := b0e35 X1 X0
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e118 : ∀ X0 : G, x = (M.op (M.op X0 y) x) := by
        intro X0
        first
        | (have i₁ := b0e75 y X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e75
        | exact resolve b0e75 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e167 : ∀ X0 : G, x ≠ x ∨ (M.op X0 y) = (k x (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e14 x (M.op X0 y)
           have i₂ := b0e118 X0
           grind)
        | exact superpose b0e118 b0e14
        | (have j0 := b0e14 x (M.op X0 y)
           grind)
        | (have r₁ := b0e14 x (M.op X0 y)
           have r₂ := b0e118 X0
           grind)
        | exact resolve b0e14 b0e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e175 : ∀ X0 : G, (M.op X0 y) = (k x (M.op X0 y)) := by
        intro X0
        first
        | (have j0 := b0e167 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e167
      have b0e290 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e18
        | exact resolve b0e18 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e292 : (σ y) = (M.op (σ x) (σ (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e22 (σ y)
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e22
        | exact resolve b0e22 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e304 : (σ y) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e46
      have b0e351 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X1) (σ X0)
           have i₂ := b0e59 X0 X1
           grind)
        | exact superpose b0e59 b0e15
        | (have j0 := b0e15 (σ X1) (σ X0)
           have j1 := b0e59 X0 X1
           grind)
        | (have r₁ := b0e15 (σ X1) (σ X0)
           have r₂ := b0e59 X0 X1
           grind)
        | (have r₁ := b0e15 (σ X0) (σ X1)
           have r₂ := b0e59 X0 X1
           grind)
        | exact resolve b0e15 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e361 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e59 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e363 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e351 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e351
      have b0e364 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e363 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e363
      have b0e368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e364 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e364
        | (have j0 := b0e364 X0 X1
           grind)
        | exact resolve b0e364 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e364
      have b0e988 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e290
           have i₂ := b0e44
           grind)
        | exact superpose b0e44 b0e290
        | exact resolve b0e290 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e290
      have b0e990 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e988
      have b0e1000 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e990
           grind)
        | exact superpose b0e990 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e990
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e990
           grind)
        | exact resolve b0e14 b0e990
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e990
      have b0e1015 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e1000
      have b0e1022 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e1015
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e1015
        | exact resolve b0e1015 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1015
      have b0e1094 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e1022
           grind)
        | exact superpose b0e1022 b0e12
        | exact resolve b0e12 b0e1022
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1022
      have b0e1125 : x = (k y x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e1094
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e1094
        | exact resolve b0e1094 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1094
      have b0e1126 : x = (k y x) := by
        first
        | (have j1 := b0e14 y x
           grind)
        | (have r₁ := b0e1125
           have r₂ := b0e14 y x
           grind)
        | exact resolve b0e1125 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1125
      have b0e1162 : y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e1126
           grind)
        | exact superpose b0e1126 b0e44
        | exact resolve b0e44 b0e1126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e1274 : x ≠ y ∨ x = (M.op x y) := by grind
      have b0e1902 : (σ y) = (σ (k (k y x) x)) ∨ (σ y) = (σ (k x (k y x))) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e368 x (k y x)
           have i₂ := b0e292
           grind)
        | exact superpose b0e292 b0e368
        | (have j0 := b0e368 x y
           grind)
        | exact resolve b0e368 b0e292
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e292 b0e368
      have b0e1991 : (σ y) = (σ (k (k y x) x)) ∨ (σ y) = (σ (k x (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have r₁ := b0e1902
           have r₂ := b0e304
           grind)
        | exact resolve b0e1902 b0e304
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e304 b0e1902
      have b0e2012 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x (k y x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e1991
           have i₂ := b0e1126
           grind)
        | exact superpose b0e1126 b0e1991
        | exact resolve b0e1991 b0e1126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1991
      have b0e2027 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e2012
           have i₂ := b0e1126
           grind)
        | exact superpose b0e1126 b0e2012
        | exact resolve b0e2012 b0e1126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1126 b0e2012
      have b0e2028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x x)) := by grind
      clear b0e2027
      have b0e2636 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e2028
           grind)
        | exact superpose b0e2028 b0e18
        | exact resolve b0e18 b0e2028
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2028
      have b0e2732 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e2636
           have i₂ := b0e1162
           grind)
        | exact superpose b0e1162 b0e2636
        | exact resolve b0e2636 b0e1162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1162 b0e2636
      have b0e2734 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by grind
      clear b0e2732
      have b0e2855 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k x x)
           have i₂ := b0e2734
           grind)
        | exact superpose b0e2734 b0e12
        | exact resolve b0e12 b0e2734
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2734
      have b0e2909 : y = (k x x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e2855
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e2855
        | exact resolve b0e2855 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2855
      have b0e3045 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e16 x x
           have i₂ := b0e2909
           grind)
        | exact superpose b0e2909 b0e16
        | (have j0 := b0e16 x x
           grind)
        | exact resolve b0e16 b0e2909
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3046 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
      clear b0e3045
      have b0e3587 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
        first
        | (have i₁ := b0e118 x
           have i₂ := b0e3046
           grind)
        | exact superpose b0e3046 b0e118
        | exact resolve b0e118 b0e3046
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3046
      have b0e3604 : y = (M.op x x) ∨ x = (M.op x x) := by grind
      clear b0e3587
      have b0e3683 : x = (M.op x y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e21 x
           have i₂ := b0e3604
           grind)
        | exact superpose b0e3604 b0e21
        | exact resolve b0e21 b0e3604
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3604
      have b0e3883 : x = (k x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e175 x
           have i₂ := b0e3683
           grind)
        | exact superpose b0e3683 b0e175
        | exact resolve b0e175 b0e3683
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e175
      have b0e3884 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e118 x
           have i₂ := b0e3683
           grind)
        | exact superpose b0e3683 b0e118
        | exact resolve b0e118 b0e3683
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118 b0e3683
      have b0e3902 : x = (M.op x x) := by grind
      clear b0e3884
      have b0e3912 : x = (k x x) := by
        first
        | (have j1 := b0e14 x x
           grind)
        | (have r₁ := b0e3883
           have r₂ := b0e14 x x
           grind)
        | exact resolve b0e3883 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3883
      have b0e4092 : x = y ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e2909
           have i₂ := b0e3912
           grind)
        | exact superpose b0e3912 b0e2909
        | exact resolve b0e2909 b0e3912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2909
      have b0e4102 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e361 x x
           have i₂ := b0e3912
           grind)
        | exact superpose b0e3912 b0e361
        | (have j0 := b0e361 x x
           grind)
        | exact resolve b0e361 b0e3912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e361 b0e3912
      have b0e4110 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e4102
      have b0e4111 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b0e4110
      have b0e4121 : x = (M.op x y) := by
        first
        | (have r₁ := b0e4092
           have r₂ := b0e1274
           grind)
        | exact resolve b0e4092 b0e1274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1274 b0e4092
      have b0e4290 : y = (M.op x x) := by
        first
        | (have i₁ := b0e21 y
           have i₂ := b0e4121
           grind)
        | exact superpose b0e4121 b0e21
        | exact resolve b0e21 b0e4121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e4121
      have b0e4317 : x = y := by
        first
        | (have i₁ := b0e4290
           have i₂ := b0e3902
           grind)
        | exact superpose b0e3902 b0e4290
        | exact resolve b0e4290 b0e3902
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4290
      have b0e4496 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e4317
           grind)
        | exact superpose b0e4317 b0e18
        | exact resolve b0e18 b0e4317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4317
      have b0e4560 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e4496
           have i₂ := b0e3902
           grind)
        | exact superpose b0e3902 b0e4496
        | exact resolve b0e4496 b0e3902
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3902 b0e4496
      have b0e4562 : False := by grind
      exact b0e4562
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : x ≠ x ∨ y = (k x y) := by
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
        have b1e32 : y = (k x y) := by grind
        clear b1e28
        have b1e40 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e44 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e45 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e46 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e45
          | exact resolve b1e45 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e32
             grind)
          | exact superpose b1e32 b1e46
          | exact resolve b1e46 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e46
        have b1e65 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e21
          | exact resolve b1e21 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ y)
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e12
          | exact resolve b1e12 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e205 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e68 (σ x)
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e68
          | exact resolve b1e68 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e68
        have b1e228 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e205
             grind)
          | exact superpose b1e205 b1e22
          | exact resolve b1e22 b1e205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e205
        have b1e238 : False := by grind
        exact b1e238
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : x ≠ x ∨ y = (k x y) := by
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
        have b2e31 : y = (k x y) := by grind
        clear b2e28
        have b2e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e292 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e75 x y
             grind)
          | exact superpose b2e75 b2e21
          | (have j1 := b2e75 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e75 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e75 y x
             grind)
          | exact resolve b2e21 b2e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e309 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e292
        have b2e314 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e309
             have r₂ := b2e22
             grind)
          | exact resolve b2e309 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e309
        have b2e320 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e314
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e314
          | exact resolve b2e314 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e314
        have b2e322 : False := by grind
        exact b2e322
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e31 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e29
        have b3e33 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e31
          | exact resolve b3e31 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e41 : y ≠ y ∨ x = (M.op y x) ∨ (M.op y x) = (k x y) := by
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
        have b3e43 : x = (M.op y x) ∨ (M.op y x) = (k x y) := by grind
        clear b3e41
        have b3e45 : (M.op y x) = (k x y) := by
          first
          | (have r₁ := b3e43
             have r₂ := b3e20
             grind)
          | exact resolve b3e43 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e51 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e13
          | exact resolve b3e13 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e52 : y = (k x y) := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e51
          | exact resolve b3e51 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e70 : y = (M.op y x) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e52
          | exact resolve b3e52 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e52
        have b3e73 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e20
          | exact resolve b3e20 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e77 : ∀ X0 : G, (M.op x (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e12
          | exact resolve b3e12 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e139 : x = (M.op x y) := by
          first
          | (have i₁ := b3e77 x
             have i₂ := b3e70
             grind)
          | exact superpose b3e70 b3e77
          | exact resolve b3e77 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e77
        have b3e178 : x = y := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e139
             grind)
          | exact superpose b3e139 b3e21
          | exact resolve b3e21 b3e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e139
        have b3e187 : False := by grind
        exact b3e187
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : y ≠ y ∨ x = (k y x) := by
            first
            | (have i₁ := b5e16 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y x
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : x = (k y x) := by grind
          clear b5e29
          have b5e37 : y ≠ y ∨ x = (M.op y x) ∨ (M.op y x) = (k x y) := by
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
          have b5e40 : x = (M.op y x) ∨ (M.op y x) = (k x y) := by grind
          clear b5e37
          have b5e41 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b5e40
               have r₂ := b5e21
               grind)
            | exact resolve b5e40 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e244 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 (σ X1) (σ X0)
               have i₂ := b5e45 X0 X1
               grind)
            | exact superpose b5e45 b5e16
            | (have j0 := b5e16 (σ X1) (σ X0)
               have j1 := b5e45 X0 X1
               grind)
            | (have r₁ := b5e16 (σ X0) (σ X1)
               have r₂ := b5e45 X0 X1
               grind)
            | (have r₁ := b5e16 (σ X1) (σ X0)
               have r₂ := b5e45 X0 X1
               grind)
            | exact resolve b5e16 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e253 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e45 x y
               grind)
            | exact superpose b5e45 b5e23
            | (have j1 := b5e45 x y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e45 x y
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e45 y x
               grind)
            | exact resolve b5e23 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e270 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e253
          have b5e275 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e270
               have r₂ := b5e24
               grind)
            | exact resolve b5e270 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e270
          have b5e276 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e244 X0 X1
               have j1 := b5e16 (σ X1) (σ X0)
               grind)
            | (have r₁ := b5e244 X0 X1
               have r₂ := b5e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b5e244 X0 X1
               have r₂ := b5e16 (σ X1) (σ X0)
               grind)
            | exact resolve b5e244 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e244
          have b5e281 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e275
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e275
            | exact resolve b5e275 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e275
          have b5e282 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e276 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e276
            | (have j0 := b5e276 X0 X1
               grind)
            | exact resolve b5e276 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e276
          have b5e342 : (σ y) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e281
               grind)
            | exact superpose b5e281 b5e24
            | exact resolve b5e24 b5e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e281
          have b5e1008 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e282 y x
               have i₂ := b5e31
               grind)
            | exact superpose b5e31 b5e282
            | (have j0 := b5e282 y x
               grind)
            | exact resolve b5e282 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e282
          have b5e1017 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e1008
          have b5e1020 : (σ y) = (σ (k x y)) := by
            first
            | (have r₁ := b5e1017
               have r₂ := b5e24
               grind)
            | exact resolve b5e1017 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1017
          have b5e1029 : (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e1020
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e1020
            | exact resolve b5e1020 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e1020
          have b5e1033 : False := by grind
          exact b5e1033
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e28 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e31 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e28
        have b6e32 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e31
          | exact resolve b6e31 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e33 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e32
             grind)
          | exact superpose b6e32 b6e13
          | exact resolve b6e13 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e34 : y = (k x y) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e33
          | exact resolve b6e33 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e63 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e34
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e34
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e34 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e65 : y = (M.op x y) ∨ x = (M.op y x) := by grind
        clear b6e63
        have b6e68 : x = (M.op y x) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e21
             grind)
          | exact resolve b6e65 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e71 : False := by grind
        exact b6e71
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) (σ x)
               grind)
            | (have r₁ := b7e16 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : (σ x) = (k (σ y) (σ x)) := by grind
          clear b7e31
          have b7e35 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e34
            | exact resolve b7e34 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e36 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e35
               grind)
            | exact superpose b7e35 b7e14
            | exact resolve b7e14 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e37 : x = (k y x) := by
            first
            | (have i₁ := b7e36
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e36
            | exact resolve b7e36 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e58 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e37
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e37
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e37 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e60 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b7e58
          have b7e63 : y = (M.op x y) := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e21
               grind)
            | exact resolve b7e60 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e66 : False := by grind
          exact b7e66
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e158 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e44 x y
               grind)
            | exact superpose b8e44 b8e23
            | (have j1 := b8e44 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e44 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e44 y x
               grind)
            | exact resolve b8e23 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e174 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e158
          have b8e179 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e174
               have r₂ := b8e24
               grind)
            | exact resolve b8e174 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e186 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e179
               grind)
            | exact superpose b8e179 b8e20
            | exact resolve b8e20 b8e179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179
          have b8e310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e186
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e186
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e186 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e311 : y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b8e310
          have b8e312 : x = (M.op y x) := by
            first
            | (have r₁ := b8e311
               have r₂ := b8e22
               grind)
            | exact resolve b8e311 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311
          have b8e313 : False := by grind
          exact b8e313

/-- `Equation1443`: `x = (x ◇ y) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyx_pxy_Equation1443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : x = y := by
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
        have b3e28 : False := by grind
        exact b3e28
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ y) ≠ (σ y) := by
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
          have b4e28 : False := by grind
          exact b4e28
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e41 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X3))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 (M.op X0 X1) (M.op X0 (M.op X0 x)) X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) := by
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
          have b5e44 : ∀ X0 : G, x = (M.op (M.op x X0) y) := by
            intro X0
            first
            | (have i₁ := b5e42 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e42
            | exact resolve b5e42 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e45 : x = (M.op y y) := by
            first
            | (have i₁ := b5e44 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e44
            | exact resolve b5e44 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e48 : y ≠ y ∨ x = y ∨ (k x y) = (M.op y x) := by
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
          have b5e51 : x = y ∨ (k x y) = (M.op y x) := by grind
          clear b5e48
          have b5e52 : (k x y) = (M.op y x) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e53 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 y
               have i₂ := b5e45
               grind)
            | exact superpose b5e45 b5e13
            | exact resolve b5e13 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e93 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) X1 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e94 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) (σ X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e114 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 X1 (M.op X0 (M.op X0 x))
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e41
            | exact resolve b5e41 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e185 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) (M.op (σ X0) X2))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) (σ X1) X2
               have i₂ := b5e56 X0 X1
               grind)
            | exact superpose b5e56 b5e13
            | (have j1 := b5e56 X0 X1
               grind)
            | exact resolve b5e13 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e253 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e114 (σ X0) (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e114
            | exact resolve b5e114 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e454 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e93 y X0
               have i₂ := b5e45
               grind)
            | exact superpose b5e45 b5e93
            | exact resolve b5e93 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e474 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e454 (σ y)
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e454
            | exact resolve b5e454 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e454
          have b5e490 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e474
               have i₂ := b5e45
               grind)
            | exact superpose b5e45 b5e474
            | exact resolve b5e474 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e474
          have b5e527 : (σ x) = (M.op (σ y) (M.op (σ x) (σ (M.op x x)))) := by
            first
            | (have i₁ := b5e93 x (M.op (σ y) (σ x))
               have i₂ := b5e490
               grind)
            | exact superpose b5e490 b5e93
            | exact resolve b5e93 b5e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e93 b5e490
          have b5e746 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b5e114 (σ y) (M.op (σ x) (σ (M.op x x)))
               have i₂ := b5e527
               grind)
            | exact superpose b5e527 b5e114
            | exact resolve b5e114 b5e527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e114 b5e527
          have b5e794 : (σ x) = (M.op (σ y) (σ (k x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e746
               have i₂ := b5e56 x y
               grind)
            | exact superpose b5e56 b5e746
            | (have j1 := b5e56 x y
               grind)
            | exact resolve b5e746 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e746
          have b5e809 : (σ x) = (M.op (σ y) (σ (k x y))) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e794
               have r₂ := b5e24
               grind)
            | exact resolve b5e794 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e794
          have b5e810 : (σ x) = (M.op (σ y) (σ (k x y))) := by
            first
            | (have r₁ := b5e809
               have r₂ := b5e23
               grind)
            | exact resolve b5e809 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e809
          have b5e811 : (σ x) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b5e810
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e810
            | exact resolve b5e810 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e810
          have b5e1042 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y x)) (M.op (σ x) (M.op (σ x) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e185 x y X0
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e185
            | (have j0 := b5e185 x y x
               grind)
            | exact resolve b5e185 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e185
          have b5e1082 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y x)) (M.op (σ x) (M.op (σ x) X0))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e1042 X0
               grind)
            | (have r₁ := b5e1042 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e1042 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1042
          have b5e1087 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y x)) (M.op (σ x) (M.op (σ x) X0))) := by
            intro X0
            first
            | (have j0 := b5e1082 X0
               grind)
            | (have r₁ := b5e1082 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e1082 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1082
          have b5e1710 : (σ y) = (M.op (σ (M.op y x)) (M.op (σ y) (σ (M.op y x)))) := by
            first
            | (have i₁ := b5e253 (M.op y x)
               have i₂ := b5e53 x
               grind)
            | exact superpose b5e53 b5e253
            | exact resolve b5e253 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e253
          have b5e1761 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
            first
            | (have i₁ := b5e1710
               have i₂ := b5e811
               grind)
            | exact superpose b5e811 b5e1710
            | exact resolve b5e1710 b5e811
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1710
          have b5e2203 : (σ (M.op y x)) = (M.op (σ (M.op (M.op y x) (M.op y x))) (M.op (σ (M.op y x)) (σ x))) := by
            first
            | (have i₁ := b5e94 (M.op y x) (M.op (σ x) (M.op (σ x) x))
               have i₂ := b5e1087 x
               grind)
            | exact superpose b5e1087 b5e94
            | exact resolve b5e94 b5e1087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94 b5e1087
          have b5e2218 : (σ (M.op y x)) = (M.op (σ (M.op (M.op y x) (M.op y x))) (σ y)) := by
            first
            | (have i₁ := b5e2203
               have i₂ := b5e1761
               grind)
            | exact superpose b5e1761 b5e2203
            | exact resolve b5e2203 b5e1761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1761 b5e2203
          have b5e2220 : (σ (M.op y x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e2218
               have i₂ := b5e53 x
               grind)
            | exact superpose b5e53 b5e2218
            | exact resolve b5e2218 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e2218
          have b5e2221 : (σ (M.op y x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e2220
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e2220
            | exact resolve b5e2220 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e2220
          have b5e2222 : (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b5e2221
               have i₂ := b5e45
               grind)
            | exact superpose b5e45 b5e2221
            | exact resolve b5e2221 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45 b5e2221
          have b5e2241 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e811
               have i₂ := b5e2222
               grind)
            | exact superpose b5e2222 b5e811
            | exact resolve b5e811 b5e2222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e811
          have b5e2248 : (M.op y x) = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 (M.op y x)
               have i₂ := b5e2222
               grind)
            | exact superpose b5e2222 b5e14
            | exact resolve b5e14 b5e2222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2222
          have b5e2305 : x = (M.op y x) := by
            first
            | (have i₁ := b5e2248
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e2248
            | exact resolve b5e2248 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2248
          have b5e2441 : x ≠ x ∨ x = y ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b5e17 y x
               have i₂ := b5e2305
               grind)
            | exact superpose b5e2305 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e2305
               grind)
            | exact resolve b5e17 b5e2305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2305
          have b5e2449 : x = y ∨ (M.op x y) = (k y x) := by grind
          clear b5e2441
          have b5e2454 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b5e2449
               have r₂ := b5e21
               grind)
            | exact resolve b5e2449 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2449
          have b5e2459 : y = (k y x) := by
            first
            | (have i₁ := b5e2454
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2454
            | exact resolve b5e2454 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2454
          have b5e2999 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e2241
               grind)
            | exact superpose b5e2241 b5e17
            | (have j0 := b5e17 (σ x) (σ y)
               grind)
            | (have r₁ := b5e17 (σ y) (σ x)
               have r₂ := b5e2241
               grind)
            | exact resolve b5e17 b5e2241
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2241
          have b5e3008 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b5e2999
          have b5e3009 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e3008
               have r₂ := b5e23
               grind)
            | exact resolve b5e3008 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3008
          have b5e3016 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e3009
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e3009
            | exact resolve b5e3009 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3009
          have b5e3018 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e3016
               have i₂ := b5e2459
               grind)
            | exact superpose b5e2459 b5e3016
            | exact resolve b5e3016 b5e2459
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2459 b5e3016
          have b5e3020 : False := by grind
          exact b5e3020
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e33 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) := by
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
          have b7e35 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
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
          have b7e37 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e35 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear b7e45
          have b7e48 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e49 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
          have b7e70 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e37 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e75 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e70
            | exact resolve b7e70 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e79 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e75
               grind)
            | exact superpose b7e75 b7e14
            | exact resolve b7e14 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e80 : x = (M.op y y) := by
            first
            | (have i₁ := b7e79
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e79
            | exact resolve b7e79 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e90 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 y
               have i₂ := b7e80
               grind)
            | exact superpose b7e80 b7e13
            | exact resolve b7e13 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e95 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) X0 (M.op (σ x) (M.op (σ x) x))
               have i₂ := b7e33 x
               grind)
            | exact superpose b7e33 b7e13
            | exact resolve b7e13 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e97 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b7e95 X0
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e95
            | exact resolve b7e95 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e101 : y = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b7e90 y
               have i₂ := b7e80
               grind)
            | exact superpose b7e80 b7e90
            | exact resolve b7e90 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e90
          have b7e126 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 (M.op y x)
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e13
            | exact resolve b7e13 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e353 : (σ y) = (M.op (σ (k x y)) (σ (k x y))) := by
            first
            | (have i₁ := b7e97 (σ x)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e97
            | exact resolve b7e97 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49 b7e97
          have b7e371 : (σ y) = (σ (M.op (k x y) (k x y))) := by
            first
            | (have i₁ := b7e353
               have i₂ := b7e31 (k x y)
               grind)
            | exact superpose b7e31 b7e353
            | exact resolve b7e353 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e353
          have b7e460 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e371
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e371
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e371 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e371
          have b7e475 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = y := by
            first
            | (have r₁ := b7e460
               have r₂ := b7e22
               grind)
            | exact resolve b7e460 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e460
          have b7e477 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have r₁ := b7e475
               have r₂ := b7e21
               grind)
            | exact resolve b7e475 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e475
          have b7e479 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e477
               have i₂ := b7e126 y
               grind)
            | exact superpose b7e126 b7e477
            | exact resolve b7e477 b7e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126 b7e477
          have b7e480 : False := by grind
          exact b7e480
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e114 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e55 x y
               grind)
            | exact superpose b8e55 b8e20
            | (have j1 := b8e55 x y
               grind)
            | exact resolve b8e20 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e124 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e114
               have r₂ := b8e24
               grind)
            | exact resolve b8e114 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e130 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e124
               have r₂ := b8e23
               grind)
            | exact resolve b8e124 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e133 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e130
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e130
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e130
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e130
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e130 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e134 : y = (M.op x y) ∨ x = y := by grind
          clear b8e133
          have b8e135 : x = y := by
            first
            | (have r₁ := b8e134
               have r₂ := b8e22
               grind)
            | exact resolve b8e134 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e136 : False := by grind
          exact b8e136

/-- `Equation1448`: `x = (x ◇ y) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1448 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1448 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1448.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e59 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e62 : False := by grind
      exact b0e62
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : x = y := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e26
          | exact resolve b3e26 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : False := by grind
        exact b3e28
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ x) ≠ (σ x) := by
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
          have b4e28 : False := by grind
          exact b4e28
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e306 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e11884 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e306 x y
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e306
            | (have j0 := b5e306 x y
               grind)
            | exact resolve b5e306 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e306
          have b5e11889 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e11884
          have b5e11893 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e11889
               have r₂ := b5e24
               grind)
            | exact resolve b5e11889 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11889
          have b5e11898 : False := by grind
          exact b5e11898
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
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
          have b7e59 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e49
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e49 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e26
               grind)
            | exact resolve b7e59 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e59
          have b7e61 : x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e62 : False := by grind
          exact b7e62
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e175 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e56 x y
               grind)
            | exact superpose b8e56 b8e20
            | (have j1 := b8e56 x y
               grind)
            | exact resolve b8e20 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e188 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e175
               have r₂ := b8e24
               grind)
            | exact resolve b8e175 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175
          have b8e193 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e188
               have r₂ := b8e23
               grind)
            | exact resolve b8e188 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188
          have b8e196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e193
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e193
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e193
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e193
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e193 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e193
          have b8e197 : x = (M.op x y) ∨ x = y := by grind
          clear b8e196
          have b8e198 : x = y := by
            first
            | (have r₁ := b8e197
               have r₂ := b8e22
               grind)
            | exact resolve b8e197 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e197
          have b8e199 : False := by grind
          exact b8e199

/-- `Equation1636`: `x = (x ◇ x) ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pxy_y_pyy_pxy_Equation1636 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1636 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1636.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
      · have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op x y) := by grind
        have b0e21 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e19
          | exact resolve b0e19 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e24 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e23
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e23
          | exact resolve b0e23 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23
        have b0e25 : False := by grind
        exact b0e25
      · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
        · have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : x = (M.op x y) := by grind
          have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e20
            | exact resolve b1e20 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e26 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b1e25
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e25
            | exact resolve b1e25 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e25
          have b1e27 : False := by grind
          exact b1e27
        · have b2e24 : (M.op y y) ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e25 : False := by grind
          exact b2e25
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : x = (M.op x y) := by grind
          have b3e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e28 : x ≠ x ∨ y = (k x y) := by
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
          have b3e31 : y = (k x y) := by grind
          clear b3e28
          have b3e35 : ∀ X0 : G, y = (M.op (M.op y y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b3e13 y x X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e38 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b3e13 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b3e13 X0 x x
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e40 : ∀ X0 : G, y = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b3e35 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e35
            | exact resolve b3e35 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e35
          have b3e46 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ x)) X0)) := by
            intro X0
            first
            | (have i₁ := b3e13 (σ y) (σ x) X0
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e49 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X0 (M.op X0 X0) X1
               have i₂ := b3e38 X0
               grind)
            | exact superpose b3e38 b3e13
            | exact resolve b3e13 b3e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e38
          have b3e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b3e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b3e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e56 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b3e54
          have b3e57 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e56
               have r₂ := b3e25
               grind)
            | exact resolve b3e56 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e56
          have b3e59 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b3e57
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e57
            | exact resolve b3e57 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e57
          have b3e60 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e59
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e59
            | exact resolve b3e59 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e59
          have b3e154 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b3e13 (M.op X0 X0) X1 X2
               have i₂ := b3e49 X0 X0
               grind)
            | exact superpose b3e49 b3e13
            | exact resolve b3e13 b3e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e177 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b3e19 X0 X0
               have i₂ := b3e55 (σ X0)
               grind)
            | exact superpose b3e55 b3e19
            | (have j1 := b3e55 (σ X0)
               grind)
            | exact resolve b3e19 b3e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e55
          have b3e202 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
            first
            | (have i₁ := b3e46 (M.op (σ x) x)
               have i₂ := b3e49 (σ x) x
               grind)
            | exact superpose b3e49 b3e46
            | exact resolve b3e46 b3e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e46 b3e49
          have b3e209 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b3e202
               have i₂ := b3e60
               grind)
            | exact superpose b3e60 b3e202
            | exact resolve b3e202 b3e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e202
          have b3e227 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b3e13 (σ x) (σ y) X0
               have i₂ := b3e209
               grind)
            | exact superpose b3e209 b3e13
            | exact resolve b3e13 b3e209
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e209
          have b3e1711 : ∀ X0 : G, (M.op x x) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b3e154 x y X0
               have i₂ := b3e40 x
               grind)
            | exact superpose b3e40 b3e154
            | exact resolve b3e154 b3e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40 b3e154
          have b3e1989 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b3e1711 y
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e1711
            | exact resolve b3e1711 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1711
          have b3e2016 : x = (M.op x x) := by
            first
            | (have i₁ := b3e1989
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e1989
            | exact resolve b3e1989 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1989
          have b3e2084 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b3e16 x x
               have i₂ := b3e2016
               grind)
            | exact superpose b3e2016 b3e16
            | (have j0 := b3e16 x x
               grind)
            | (have r₁ := b3e16 x x
               have r₂ := b3e2016
               grind)
            | exact resolve b3e16 b3e2016
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e2016
          have b3e2090 : x = (k x x) := by grind
          clear b3e2084
          have b3e3394 : ∀ X0 : G, (σ x) = (M.op (σ (k x x)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            intro X0
            first
            | (have i₁ := b3e227 X0
               have i₂ := b3e177 x
               grind)
            | exact superpose b3e177 b3e227
            | (have j1 := b3e177 x
               grind)
            | exact resolve b3e227 b3e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e177 b3e227
          have b3e3462 : ∀ X0 : G, (σ x) = (M.op (σ (k x x)) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have j0 := b3e3394 X0
               grind)
            | (have r₁ := b3e3394 X0
               have r₂ := b3e25
               grind)
            | exact resolve b3e3394 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e3394
          have b3e3463 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b3e3462 X0
               have i₂ := b3e2090
               grind)
            | exact superpose b3e2090 b3e3462
            | exact resolve b3e3462 b3e2090
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e2090 b3e3462
          have b3e3624 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e3463 (σ y)
               have i₂ := b3e60
               grind)
            | exact superpose b3e60 b3e3463
            | exact resolve b3e3463 b3e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e60 b3e3463
          have b3e3705 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e23
               have i₂ := b3e3624
               grind)
            | exact superpose b3e3624 b3e23
            | exact resolve b3e23 b3e3624
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e3624
          have b3e3724 : False := by grind
          exact b3e3724
        · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
          · have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : x = (M.op x y) := by grind
            have b4e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            have b4e25 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : x ≠ x ∨ y = (k x y) := by
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
            have b4e29 : y = (k x y) := by grind
            clear b4e28
            have b4e51 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b4e18 (σ x) X0
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 (σ x) X0
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e76 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b4e18 X0 X0
                 have i₂ := b4e19 X0 X1
                 grind)
              | (have i₁ := b4e18 X0 X1
                 have i₂ := b4e19 X0 X1
                 grind)
              | exact superpose b4e19 b4e18
              | (have j0 := b4e18 X0 X1
                 have j1 := b4e19 X0 X1
                 grind)
              | (have r₁ := b4e18 X0 X1
                 have r₂ := b4e19 X0 X1
                 grind)
              | (have r₁ := b4e18 X1 X1
                 have r₂ := b4e19 X1 X1
                 grind)
              | exact resolve b4e18 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b4e76 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e76
            have b4e89 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              first
              | (have j0 := b4e88 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e88
            have b4e867 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b4e51 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e51
            have b4e871 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e867
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e867 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e867
            have b4e875 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b4e871
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e871
              | exact resolve b4e871 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e871
            have b4e879 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e875
                 have i₂ := b4e29
                 grind)
              | exact superpose b4e29 b4e875
              | exact resolve b4e875 b4e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e29 b4e875
            have b4e904 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b4e17 (σ y) (σ y)
                 have i₂ := b4e879
                 grind)
              | exact superpose b4e879 b4e17
              | (have j0 := b4e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b4e17 (σ y) (σ y)
                 have r₂ := b4e879
                 grind)
              | exact resolve b4e17 b4e879
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e879
            have b4e909 : (σ y) = (k (σ y) (σ y)) := by grind
            clear b4e904
            have b4e916 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b4e909
                 have i₂ := b4e20 y y
                 grind)
              | exact superpose b4e20 b4e909
              | exact resolve b4e909 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e909
            have b4e936 : (k y y) = (τ (σ y)) := by
              first
              | (have i₁ := b4e15 (k y y)
                 have i₂ := b4e916
                 grind)
              | exact superpose b4e916 b4e15
              | exact resolve b4e15 b4e916
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e916
            have b4e937 : y = (k y y) := by
              first
              | (have i₁ := b4e936
                 have i₂ := b4e15 y
                 grind)
              | exact superpose b4e15 b4e936
              | exact resolve b4e936 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e936
            have b4e1087 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b4e89 y y
                 have i₂ := b4e937
                 grind)
              | exact superpose b4e937 b4e89
              | (have j0 := b4e89 y y
                 grind)
              | exact resolve b4e89 b4e937
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e89 b4e937
            have b4e1088 : y = (M.op y y) := by grind
            clear b4e1087
            have b4e1095 : False := by grind
            exact b4e1095
          · have b5e26 : (M.op y y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : False := by grind
            exact b5e27
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : x = (M.op x y) := by grind
          have b6e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : x ≠ x ∨ y = (k x y) := by
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
          have b6e29 : y = (k x y) := by grind
          clear b6e26
          have b6e33 : ∀ X0 : G, y = (M.op (M.op y y) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b6e13 y x X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e36 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e13 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b6e13 X0 x x
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : ∀ X0 : G, y = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b6e33 X0
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e33
            | exact resolve b6e33 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33
          have b6e45 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X0 (M.op X0 X0) X1
               have i₂ := b6e36 X0
               grind)
            | exact superpose b6e36 b6e13
            | exact resolve b6e13 b6e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e36
          have b6e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b6e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e54 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x X0)) (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 (M.op x X0) y X1
               have i₂ := b6e38 X0
               grind)
            | exact superpose b6e38 b6e13
            | exact resolve b6e13 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38
          have b6e61 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X0 X1
               have i₂ := b6e18 (σ X0) (σ X1)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X0) (σ X1)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e150 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b6e19 X0 X0
               have i₂ := b6e50 (σ X0)
               grind)
            | exact superpose b6e50 b6e19
            | (have j1 := b6e50 (σ X0)
               grind)
            | exact resolve b6e19 b6e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e50
          have b6e807 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e61 x y
               grind)
            | exact superpose b6e61 b6e23
            | (have j1 := b6e61 x y
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e61 x y
               grind)
            | exact resolve b6e23 b6e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e61
          have b6e868 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b6e807
          have b6e874 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b6e868
               have r₂ := b6e22
               grind)
            | exact resolve b6e868 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e868
          have b6e883 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e874
               have i₂ := b6e29
               grind)
            | exact superpose b6e29 b6e874
            | exact resolve b6e874 b6e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e29 b6e874
          have b6e900 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have i₁ := b6e45 (σ x) (σ y)
               have i₂ := b6e883
               grind)
            | exact superpose b6e883 b6e45
            | exact resolve b6e45 b6e883
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e883
          have b6e1421 : ∀ X0 : G, (M.op x x) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b6e54 x X0
               have i₂ := b6e45 x x
               grind)
            | exact superpose b6e45 b6e54
            | exact resolve b6e54 b6e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e45 b6e54
          have b6e1473 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b6e1421 y
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e1421
            | exact resolve b6e1421 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1421
          have b6e1497 : x = (M.op x x) := by
            first
            | (have i₁ := b6e1473
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e1473
            | exact resolve b6e1473 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1473
          have b6e1561 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b6e16 x x
               have i₂ := b6e1497
               grind)
            | exact superpose b6e1497 b6e16
            | (have j0 := b6e16 x x
               grind)
            | (have r₁ := b6e16 x x
               have r₂ := b6e1497
               grind)
            | exact resolve b6e16 b6e1497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1497
          have b6e1566 : x = (k x x) := by grind
          clear b6e1561
          have b6e2312 : (σ x) = (M.op (σ (k x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e900
               have i₂ := b6e150 x
               grind)
            | exact superpose b6e150 b6e900
            | (have j1 := b6e150 x
               grind)
            | exact resolve b6e900 b6e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e150
          have b6e2358 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e2312
               have i₂ := b6e1566
               grind)
            | exact superpose b6e1566 b6e2312
            | exact resolve b6e2312 b6e1566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1566 b6e2312
          have b6e2363 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b6e2358
               have r₂ := b6e22
               grind)
            | exact resolve b6e2358 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2358
          have b6e2371 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e900
               have i₂ := b6e2363
               grind)
            | exact superpose b6e2363 b6e900
            | exact resolve b6e900 b6e2363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e900 b6e2363
          have b6e2410 : False := by grind
          exact b6e2410
        · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
              intro X0 X1 X2
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : x = (M.op x y) := by grind
            have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : x ≠ x ∨ y = (k x y) := by
              first
              | (have i₁ := b7e17 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 x y
                 grind)
              | (have r₁ := b7e17 x y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e29 : y = (k x y) := by grind
            clear b7e28
            have b7e38 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e14 X0 X0 (M.op (M.op x X0) x)
                 have i₂ := b7e14 X0 x x
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e40 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X0 (M.op X0 X0) X1
                 have i₂ := b7e38 X0
                 grind)
              | exact superpose b7e38 b7e14
              | exact resolve b7e14 b7e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38
            have b7e70 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b7e24
                 have i₂ := b7e19 (σ x) X0
                 grind)
              | (have i₁ := b7e24
                 have i₂ := b7e19 (σ x) (σ x)
                 grind)
              | exact superpose b7e19 b7e24
              | (have j1 := b7e19 (σ x) X0
                 grind)
              | (have r₁ := b7e24
                 have r₂ := b7e19 (σ x) (σ y)
                 grind)
              | exact resolve b7e24 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e97 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e14 (M.op X0 X0) X1 X2
                 have i₂ := b7e40 X0 X0
                 grind)
              | exact superpose b7e40 b7e14
              | exact resolve b7e14 b7e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e461 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e97 X0 (M.op X0 X0) X1
                 have i₂ := b7e40 X0 X0
                 grind)
              | exact superpose b7e40 b7e97
              | exact resolve b7e97 b7e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40 b7e97
            have b7e851 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b7e70 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e70
            have b7e853 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e851
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e851 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e851
            have b7e855 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e853
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e853
              | exact resolve b7e853 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e853
            have b7e857 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b7e855
                 have i₂ := b7e29
                 grind)
              | exact superpose b7e29 b7e855
              | exact resolve b7e855 b7e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e855
            have b7e994 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e461 (σ x) (σ y)
                 have i₂ := b7e857
                 grind)
              | exact superpose b7e857 b7e461
              | exact resolve b7e461 b7e857
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e461 b7e857
            have b7e996 : False := by grind
            exact b7e996
          · have b8e26 : (M.op y y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : False := by grind
            exact b8e27
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : x ≠ (M.op x y) := by grind
          have b9e22 : (M.op x y) = (M.op x x) := by grind
          have b9e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e20
            | exact resolve b9e20 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e27 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e26
            | exact resolve b9e26 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e45 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b9e13 (σ y) (σ x) X0
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e13
            | exact resolve b9e13 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e46 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e13 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
               have i₂ := b9e13 X0 X1 X2
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e47 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b9e13 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b9e13 X0 x x
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b9e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e91 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 (M.op X0 X0) X1
               have i₂ := b9e47 X0
               grind)
            | exact superpose b9e47 b9e13
            | exact resolve b9e13 b9e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e47
          have b9e153 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
            first
            | (have i₁ := b9e45 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e45
            | exact resolve b9e45 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e45
          have b9e189 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b9e13 (M.op X0 X0) X1 X2
               have i₂ := b9e91 X0 X0
               grind)
            | exact superpose b9e91 b9e13
            | exact resolve b9e13 b9e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e91
          have b9e1598 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e189 X1 (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X3
               have i₂ := b9e46 X1 X0 X2 X1
               grind)
            | exact superpose b9e46 b9e189
            | exact resolve b9e189 b9e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e46 b9e189
          have b9e2421 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b9e1598 X0 X1 (M.op X0 X1) (M.op (M.op x (M.op X0 X1)) x)
               have i₂ := b9e13 (M.op X0 X1) x x
               grind)
            | exact superpose b9e13 b9e1598
            | exact resolve b9e1598 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e1598
          have b9e2540 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e2421 (M.op (σ y) (σ y)) (σ x)
               have i₂ := b9e153
               grind)
            | exact superpose b9e153 b9e2421
            | exact resolve b9e2421 b9e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e153 b9e2421
          have b9e2629 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e2540
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e2540
            | exact resolve b9e2540 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e2540
          have b9e2671 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ x)
               have i₂ := b9e2629
               grind)
            | exact superpose b9e2629 b9e16
            | (have j0 := b9e16 (σ x) (σ x)
               grind)
            | (have r₁ := b9e16 (σ x) (σ x)
               have r₂ := b9e2629
               grind)
            | exact resolve b9e16 b9e2629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e2629
          have b9e2680 : (σ x) = (k (σ x) (σ x)) := by grind
          clear b9e2671
          have b9e2692 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b9e2680
               have i₂ := b9e19 x x
               grind)
            | exact superpose b9e19 b9e2680
            | exact resolve b9e2680 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e2680
          have b9e2855 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b9e2692
               have i₂ := b9e53 x
               grind)
            | exact superpose b9e53 b9e2692
            | (have j1 := b9e53 x
               grind)
            | exact resolve b9e2692 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e53 b9e2692
          have b9e2890 : x = (M.op x x) := by
            first
            | (have r₁ := b9e2855
               have r₂ := b9e27
               grind)
            | exact resolve b9e2855 b9e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27 b9e2855
          have b9e2893 : False := by grind
          exact b9e2893
        · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : x ≠ (M.op x y) := by grind
            have b10e23 : (M.op x y) = (M.op x x) := by grind
            have b10e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
            have b10e25 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b10e30 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b10e29
            have b10e31 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b10e30
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e30
              | exact resolve b10e30 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e30
            have b10e32 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e31
                 grind)
              | exact superpose b10e31 b10e15
              | exact resolve b10e15 b10e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e31
            have b10e33 : y = (k x y) := by
              first
              | (have i₁ := b10e32
                 have i₂ := b10e15 y
                 grind)
              | exact superpose b10e15 b10e32
              | exact resolve b10e32 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32
            have b10e50 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
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
            have b10e271 : x = (M.op x y) ∨ (M.op y y) = (k x y) := by
              first
              | (have j0 := b10e50 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e50
            have b10e274 : (M.op y y) = (k x y) := by
              first
              | (have r₁ := b10e271
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e271 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e271
            have b10e277 : y = (M.op y y) := by
              first
              | (have i₁ := b10e274
                 have i₂ := b10e33
                 grind)
              | exact superpose b10e33 b10e274
              | exact resolve b10e274 b10e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33 b10e274
            have b10e280 : False := by grind
            exact b10e280
          · have b11e26 : (M.op y y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : False := by grind
            exact b11e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b12e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : x ≠ (M.op x y) := by grind
            have b12e23 : (M.op x y) = (M.op x x) := by grind
            have b12e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e27 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b12e24
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e24
              | exact resolve b12e24 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e28 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e22
              | exact resolve b12e22 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e30 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b12e29
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e29
              | exact resolve b12e29 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29
            have b12e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b12e18 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e145 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b12e20 X0 X0
                 have i₂ := b12e62 (σ X0)
                 grind)
              | exact superpose b12e62 b12e20
              | (have j1 := b12e62 (σ X0)
                 grind)
              | exact resolve b12e20 b12e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e3801 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b12e30
                 have i₂ := b12e145 x
                 grind)
              | exact superpose b12e145 b12e30
              | (have j1 := b12e145 x
                 grind)
              | exact resolve b12e30 b12e145
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e30 b12e145
            have b12e3875 : (σ (M.op x x)) ≠ (σ (k x x)) := by
              first
              | (have r₁ := b12e3801
                 have r₂ := b12e27
                 grind)
              | exact resolve b12e3801 b12e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e27 b12e3801
            have b12e3897 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b12e3875
                 have i₂ := b12e62 x
                 grind)
              | exact superpose b12e62 b12e3875
              | (have j1 := b12e62 x
                 grind)
              | exact resolve b12e3875 b12e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e62 b12e3875
            have b12e3902 : x = (M.op x x) := by grind
            clear b12e3897
            have b12e3905 : False := by grind
            exact b12e3905
          · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
            · have b13e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e23 : x ≠ (M.op x y) := by grind
              have b13e24 : (M.op x y) = (M.op x x) := by grind
              have b13e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e50 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) := by
                first
                | (have i₁ := b13e19 x x
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
              have b13e52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b13e19 (σ x) (σ x)
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
              have b13e54 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
              clear b13e52
              have b13e55 : x = (M.op x y) ∨ (M.op x y) = (k x x) := by grind
              clear b13e50
              have b13e56 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
                first
                | (have r₁ := b13e54
                   have r₂ := b13e25
                   grind)
                | exact resolve b13e54 b13e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e54
              have b13e58 : (M.op x y) = (k x x) := by
                first
                | (have r₁ := b13e55
                   have r₂ := b13e23
                   grind)
                | exact resolve b13e55 b13e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e55
              have b13e59 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
                first
                | (have i₁ := b13e56
                   have i₂ := b13e21 x x
                   grind)
                | exact superpose b13e21 b13e56
                | exact resolve b13e56 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e56
              have b13e60 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e59
                   have i₂ := b13e58
                   grind)
                | exact superpose b13e58 b13e59
                | exact resolve b13e59 b13e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e58 b13e59
              have b13e61 : False := by grind
              exact b13e61
            · have b14e28 : (M.op y y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : False := by grind
              exact b14e29
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
              intro X0 X1 X2
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : x ≠ (M.op x y) := by grind
            have b15e23 : (M.op x y) = (M.op x x) := by grind
            have b15e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e22
              | exact resolve b15e22 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e42 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e14 X0 X0 (M.op (M.op x X0) x)
                 have i₂ := b15e14 X0 x x
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e52 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 (M.op X0 X0) X1
                 have i₂ := b15e42 X0
                 grind)
              | exact superpose b15e42 b15e14
              | exact resolve b15e14 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e42
            have b15e55 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (M.op y y) = (k x y) := by
              first
              | (have i₁ := b15e18 x y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e18
              | (have j0 := b15e18 x x
                 grind)
              | (have r₁ := b15e18 x y
                 have r₂ := b15e23
                 grind)
              | exact resolve b15e18 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e58 : x = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
            clear b15e55
            have b15e60 : (M.op y y) = (k x y) := by
              first
              | (have r₁ := b15e58
                 have r₂ := b15e27
                 grind)
              | exact resolve b15e58 b15e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27 b15e58
            have b15e61 : y = (k x y) := by
              first
              | (have i₁ := b15e60
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e60
              | exact resolve b15e60 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e60
            have b15e66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X0 X1
                 have i₂ := b15e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e169 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 (M.op X0 X0) X1 X2
                 have i₂ := b15e52 X0 X0
                 grind)
              | exact superpose b15e52 b15e14
              | exact resolve b15e14 b15e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e776 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e66 x y
                 grind)
              | exact superpose b15e66 b15e25
              | (have j1 := b15e66 x y
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e66 x y
                 grind)
              | exact resolve b15e25 b15e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e66
            have b15e836 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
            clear b15e776
            have b15e843 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b15e836
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e836 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e836
            have b15e853 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e843
                 have i₂ := b15e61
                 grind)
              | exact superpose b15e61 b15e843
              | exact resolve b15e843 b15e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e61 b15e843
            have b15e1608 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e169 X0 (M.op X0 X0) X1
                 have i₂ := b15e52 X0 X0
                 grind)
              | exact superpose b15e52 b15e169
              | exact resolve b15e169 b15e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e52 b15e169
            have b15e1752 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e1608 (σ x) (σ y)
                 have i₂ := b15e853
                 grind)
              | exact superpose b15e853 b15e1608
              | exact resolve b15e1608 b15e853
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e853 b15e1608
            have b15e1806 : False := by grind
            exact b15e1806
          · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
                intro X0 X1 X2
                grind
              have b16e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e23 : x ≠ (M.op x y) := by grind
              have b16e24 : (M.op x y) = (M.op x x) := by grind
              have b16e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b16e26 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
              have b16e27 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
                   have i₂ := b16e15 X0 X1 X2
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e35 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b16e15 X0 X0 (M.op (M.op x X0) x)
                   have i₂ := b16e15 X0 x x
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e37 : x = (M.op (M.op x y) x) := by
                first
                | (have i₁ := b16e35 x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e35
                | exact resolve b16e35 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e38 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 (M.op X0 X0) X1
                   have i₂ := b16e35 X0
                   grind)
                | exact superpose b16e35 b16e15
                | exact resolve b16e15 b16e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e43 : y = (M.op (M.op y y) x) := by
                first
                | (have i₁ := b16e15 y x x
                   have i₂ := b16e37
                   grind)
                | exact superpose b16e37 b16e15
                | exact resolve b16e15 b16e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e37
              have b16e44 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
                intro X0
                first
                | (have i₁ := b16e19 x X0
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x X0
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e46 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (M.op X0 X0) (M.op (M.op X1 X0) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e19 (M.op X0 X0) (M.op (M.op X1 X0) X2)
                   have i₂ := b16e15 X0 X1 X2
                   grind)
                | exact superpose b16e15 b16e19
                | (have j0 := b16e19 X0 X0
                   grind)
                | exact resolve b16e19 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
                intro X0
                first
                | (have j0 := b16e19 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e49 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) = (k (M.op X0 X0) (M.op (M.op X1 X0) X2)) ∨ (M.op X0 X0) = X0 := by
                intro X0 X1 X2
                first
                | (have j0 := b16e46 X0 X1 X2
                   grind)
                | (have r₁ := b16e46 X1 X1 X2
                   have r₂ := b16e38 X1 X1
                   grind)
                | exact resolve b16e46 b16e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e46
              have b16e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b16e19 X0 X0
                   have i₂ := b16e20 X0 X1
                   grind)
                | (have i₁ := b16e19 X0 X1
                   have i₂ := b16e20 X0 X1
                   grind)
                | exact superpose b16e20 b16e19
                | (have j0 := b16e19 X0 X1
                   have j1 := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e19 X0 X1
                   have r₂ := b16e20 X0 X1
                   grind)
                | (have r₁ := b16e19 X1 X1
                   have r₂ := b16e20 X1 X1
                   grind)
                | exact resolve b16e19 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e62 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b16e26
                   have i₂ := b16e20 (σ x) X0
                   grind)
                | (have i₁ := b16e26
                   have i₂ := b16e20 (σ x) (σ x)
                   grind)
                | exact superpose b16e20 b16e26
                | (have j1 := b16e20 (σ x) X0
                   grind)
                | (have r₁ := b16e26
                   have r₂ := b16e20 (σ x) (σ y)
                   grind)
                | exact resolve b16e26 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b16e58 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e58
              have b16e71 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b16e70 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e70
              have b16e99 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e15 (M.op X0 X0) X1 X2
                   have i₂ := b16e38 X0 X0
                   grind)
                | exact superpose b16e38 b16e15
                | exact resolve b16e15 b16e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e196 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b16e21 X0 X0
                   have i₂ := b16e47 (σ X0)
                   grind)
                | exact superpose b16e47 b16e21
                | (have j1 := b16e47 (σ X0)
                   grind)
                | exact resolve b16e21 b16e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e47
              have b16e241 : x = (M.op x y) ∨ (M.op y y) = (k x y) := by
                first
                | (have j0 := b16e44 y
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e44
              have b16e244 : (M.op y y) = (k x y) := by
                first
                | (have r₁ := b16e241
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e241 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e241
              have b16e258 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e71 (M.op X0 X0) (M.op (M.op X1 X0) X2)
                   have i₂ := b16e15 X0 X1 X2
                   grind)
                | exact superpose b16e15 b16e71
                | (have j0 := b16e71 X0 X0
                   grind)
                | exact resolve b16e71 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e71
              have b16e868 : (M.op y y) = (k (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b16e49 y y x
                   have i₂ := b16e43
                   grind)
                | exact superpose b16e43 b16e49
                | (have j0 := b16e49 y x x
                   grind)
                | exact resolve b16e49 b16e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e49
              have b16e924 : (M.op y y) = (k (M.op y y) y) := by
                first
                | (have r₁ := b16e868
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e868 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e868
              have b16e973 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b16e62 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e62
              have b16e975 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b16e973
                   have r₂ := b16e25
                   grind)
                | exact resolve b16e973 b16e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e973
              have b16e977 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b16e975
                   have i₂ := b16e21 x y
                   grind)
                | exact superpose b16e21 b16e975
                | exact resolve b16e975 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e975
              have b16e979 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e977
                   have i₂ := b16e244
                   grind)
                | exact superpose b16e244 b16e977
                | exact resolve b16e977 b16e244
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e244 b16e977
              have b16e1897 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b16e99 X0 (M.op X0 X0) X1
                   have i₂ := b16e38 X0 X0
                   grind)
                | exact superpose b16e38 b16e99
                | exact resolve b16e99 b16e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e38
              have b16e1901 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op (M.op X0 X1) X2) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e99 X1 (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X3
                   have i₂ := b16e34 X1 X0 X2 X1
                   grind)
                | exact superpose b16e34 b16e99
                | exact resolve b16e99 b16e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34 b16e99
              have b16e2045 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op y y))) := by
                first
                | (have i₁ := b16e1897 (σ x) (σ y)
                   have i₂ := b16e979
                   grind)
                | exact superpose b16e979 b16e1897
                | exact resolve b16e1897 b16e979
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1897
              have b16e2904 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e1901 (M.op X0 X0) X0 X1 X2
                   have i₂ := b16e35 X0
                   grind)
                | exact superpose b16e35 b16e1901
                | exact resolve b16e1901 b16e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e35 b16e1901
              have b16e3316 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op y y)) X0)) := by
                intro X0
                first
                | (have i₁ := b16e2904 (σ x) (σ y) X0
                   have i₂ := b16e979
                   grind)
                | exact superpose b16e979 b16e2904
                | exact resolve b16e2904 b16e979
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e979 b16e2904
              have b16e12401 : y = (k (M.op y y) y) ∨ y = (k (M.op y y) (M.op y y)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b16e258 y y x
                   have i₂ := b16e43
                   grind)
                | exact superpose b16e43 b16e258
                | (have j0 := b16e258 y x x
                   grind)
                | exact resolve b16e258 b16e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e43 b16e258
              have b16e12524 : y = (k (M.op y y) y) ∨ y = (k (M.op y y) (M.op y y)) := by
                first
                | (have r₁ := b16e12401
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e12401 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e12401
              have b16e12624 : y = (M.op y y) ∨ y = (k (M.op y y) (M.op y y)) := by
                first
                | (have i₁ := b16e12524
                   have i₂ := b16e924
                   grind)
                | exact superpose b16e924 b16e12524
                | exact resolve b16e12524 b16e924
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e924 b16e12524
              have b16e12696 : y = (k (M.op y y) (M.op y y)) := by
                first
                | (have r₁ := b16e12624
                   have r₂ := b16e27
                   grind)
                | exact resolve b16e12624 b16e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e12624
              have b16e148024 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (k (M.op y y) (M.op y y)))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
                first
                | (have i₁ := b16e3316 (σ (M.op y y))
                   have i₂ := b16e196 (M.op y y)
                   grind)
                | exact superpose b16e196 b16e3316
                | (have j1 := b16e196 (M.op y y)
                   grind)
                | exact resolve b16e3316 b16e196
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e196 b16e3316
              have b16e148117 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
                first
                | (have i₁ := b16e148024
                   have i₂ := b16e12696
                   grind)
                | exact superpose b16e12696 b16e148024
                | exact resolve b16e148024 b16e12696
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e148024
              have b16e148122 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
                first
                | (have r₁ := b16e148117
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e148117 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e148117
              have b16e148628 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ (M.op y y)) (σ (M.op y y))) := by
                first
                | (have i₁ := b16e18 (σ (M.op y y)) (σ (M.op y y))
                   have i₂ := b16e148122
                   grind)
                | exact superpose b16e148122 b16e18
                | (have j0 := b16e18 (σ (M.op y y)) (σ (M.op y y))
                   grind)
                | (have r₁ := b16e18 (σ (M.op y y)) (σ (M.op y y))
                   have r₂ := b16e148122
                   grind)
                | exact resolve b16e18 b16e148122
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e148122
              have b16e148678 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ (M.op y y))) := by grind
              clear b16e148628
              have b16e148709 : (σ (M.op y y)) = (σ (k (M.op y y) (M.op y y))) := by
                first
                | (have i₁ := b16e148678
                   have i₂ := b16e21 (M.op y y) (M.op y y)
                   grind)
                | exact superpose b16e21 b16e148678
                | exact resolve b16e148678 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e148678
              have b16e148746 : (σ y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b16e148709
                   have i₂ := b16e12696
                   grind)
                | exact superpose b16e12696 b16e148709
                | exact resolve b16e148709 b16e12696
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e12696 b16e148709
              have b16e149286 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b16e2045
                   have i₂ := b16e148746
                   grind)
                | exact superpose b16e148746 b16e2045
                | exact resolve b16e2045 b16e148746
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e2045 b16e148746
              have b16e149351 : False := by grind
              exact b16e149351
            · have b17e28 : (M.op y y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : False := by grind
              exact b17e29
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : x ≠ (M.op x y) := by grind
          have b18e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b18e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e27 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b18e28 : (σ y) = (k (σ x) (σ y)) := by grind
          clear b18e27
          have b18e30 : (σ y) = (σ (k x y)) := by
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
          have b18e35 : (k x y) = (τ (σ y)) := by
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
          have b18e36 : y = (k x y) := by
            first
            | (have i₁ := b18e35
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e35
            | exact resolve b18e35 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e43 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e13 X0 X0 (M.op (M.op x X0) x)
               have i₂ := b18e13 X0 x x
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e58 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
          have b18e79 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b18e58
               have r₂ := b18e22
               grind)
            | exact resolve b18e58 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e58
          have b18e83 : y = (M.op x y) := by
            first
            | (have r₁ := b18e79
               have r₂ := b18e21
               grind)
            | exact resolve b18e79 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e79
          have b18e95 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X0 (M.op X0 X0) X1
               have i₂ := b18e43 X0
               grind)
            | exact superpose b18e43 b18e13
            | exact resolve b18e13 b18e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43
          have b18e176 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 (M.op X0 X0) X1 X2
               have i₂ := b18e95 X0 X0
               grind)
            | exact superpose b18e95 b18e13
            | exact resolve b18e13 b18e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1521 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e176 X0 (M.op X0 X0) X1
               have i₂ := b18e95 X0 X0
               grind)
            | exact superpose b18e95 b18e176
            | exact resolve b18e176 b18e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e95 b18e176
          have b18e1664 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b18e1521 x y
               have i₂ := b18e83
               grind)
            | exact superpose b18e83 b18e1521
            | exact resolve b18e1521 b18e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e83 b18e1521
          have b18e1713 : False := by grind
          exact b18e1713
        · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : x ≠ (M.op x y) := by grind
            have b19e23 : (M.op x y) ≠ (M.op x x) := by grind
            have b19e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b19e29 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b19e28
            have b19e30 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b19e29
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e29
              | exact resolve b19e29 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e29
            have b19e31 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e30
                 grind)
              | exact superpose b19e30 b19e15
              | exact resolve b19e15 b19e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : y = (k x y) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e31
              | exact resolve b19e31 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e41 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b19e14 X0 X0 (M.op (M.op x X0) x)
                 have i₂ := b19e14 X0 x x
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e43 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 (M.op X0 X0) X1
                 have i₂ := b19e41 X0
                 grind)
              | exact superpose b19e41 b19e14
              | exact resolve b19e14 b19e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e41
            have b19e56 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 (M.op X0 X0) X1 X2
                 have i₂ := b19e43 X0 X0
                 grind)
              | exact superpose b19e43 b19e14
              | exact resolve b19e14 b19e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e68 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b19e32
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e32
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e32 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e95 : y = (M.op x y) ∨ x = (M.op x y) := by
              first
              | (have r₁ := b19e68
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e68 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e68
            have b19e98 : y = (M.op x y) := by
              first
              | (have r₁ := b19e95
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e95 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e95
            have b19e879 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e56 X0 (M.op X0 X0) X1
                 have i₂ := b19e43 X0 X0
                 grind)
              | exact superpose b19e43 b19e56
              | exact resolve b19e56 b19e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e43 b19e56
            have b19e1242 : (M.op x y) = (M.op x x) := by
              first
              | (have i₁ := b19e879 x y
                 have i₂ := b19e98
                 grind)
              | exact superpose b19e98 b19e879
              | exact resolve b19e879 b19e98
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e98 b19e879
            have b19e1277 : False := by grind
            exact b19e1277
          · have b20e26 : (M.op y y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : False := by grind
            exact b20e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : x ≠ (M.op x y) := by grind
            have b21e23 : (M.op x y) ≠ (M.op x x) := by grind
            have b21e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b21e25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            have b21e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e24
              | exact resolve b21e24 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e29 : y ≠ y ∨ y = (k y y) := by
              first
              | (have i₁ := b21e17 y y
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e17
              | (have j0 := b21e17 y y
                 grind)
              | (have r₁ := b21e17 y y
                 have r₂ := b21e26
                 grind)
              | exact resolve b21e17 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e30 : y = (k y y) := by grind
            clear b21e29
            have b21e40 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b21e14 X0 X0 (M.op (M.op x X0) x)
                 have i₂ := b21e14 X0 x x
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e50 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X0 (M.op X0 X0) X1
                 have i₂ := b21e40 X0
                 grind)
              | exact superpose b21e40 b21e14
              | exact resolve b21e14 b21e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e40
            have b21e55 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e18
              | (have j0 := b21e18 (σ x) (σ x)
                 grind)
              | (have r₁ := b21e18 (σ x) (σ y)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e18 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e57 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
            clear b21e55
            have b21e58 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e57
                 have r₂ := b21e27
                 grind)
              | exact resolve b21e57 b21e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e27 b21e57
            have b21e60 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b21e58
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e58
              | exact resolve b21e58 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e58
            have b21e128 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 (M.op X0 X0) X1 X2
                 have i₂ := b21e50 X0 X0
                 grind)
              | exact superpose b21e50 b21e14
              | exact resolve b21e14 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e143 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ y) (σ y)
                 have i₂ := b21e60
                 grind)
              | exact superpose b21e60 b21e18
              | exact resolve b21e18 b21e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e60
            have b21e146 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by grind
            clear b21e143
            have b21e148 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b21e146
                 have i₂ := b21e20 y y
                 grind)
              | exact superpose b21e20 b21e146
              | exact resolve b21e146 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e146
            have b21e149 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b21e148
                 have i₂ := b21e30
                 grind)
              | exact superpose b21e30 b21e148
              | exact resolve b21e148 b21e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e30 b21e148
            have b21e150 : (σ y) = (σ (k x y)) := by grind
            clear b21e149
            have b21e154 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e150
                 grind)
              | exact superpose b21e150 b21e15
              | exact resolve b21e15 b21e150
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e150
            have b21e155 : y = (k x y) := by
              first
              | (have i₁ := b21e154
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e154
              | exact resolve b21e154 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e154
            have b21e171 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e155
                 grind)
              | exact superpose b21e155 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e155
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e155
            have b21e172 : y = (M.op x y) ∨ x = (M.op x y) := by
              first
              | (have r₁ := b21e171
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e171 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e171
            have b21e174 : y = (M.op x y) := by
              first
              | (have r₁ := b21e172
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e172 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e172
            have b21e2573 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e128 X0 (M.op X0 X0) X1
                 have i₂ := b21e50 X0 X0
                 grind)
              | exact superpose b21e50 b21e128
              | exact resolve b21e128 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50 b21e128
            have b21e2727 : (M.op x y) = (M.op x x) := by
              first
              | (have i₁ := b21e2573 x y
                 have i₂ := b21e174
                 grind)
              | exact superpose b21e174 b21e2573
              | exact resolve b21e2573 b21e174
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e174 b21e2573
            have b21e2788 : False := by grind
            exact b21e2788
          · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X0) X2)) = X0 := by
                intro X0 X1 X2
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : x ≠ (M.op x y) := by grind
              have b22e24 : (M.op x y) ≠ (M.op x x) := by grind
              have b22e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b22e26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
              have b22e27 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X1 X0) X2)) (M.op X0 X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 (M.op (M.op X1 X0) X2) (M.op X0 X0) X3
                   have i₂ := b22e15 X0 X1 X2
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e32 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
                intro X0
                first
                | (have i₁ := b22e15 X0 X0 (M.op (M.op x X0) x)
                   have i₂ := b22e15 X0 x x
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e34 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 (M.op X0 X0) X1
                   have i₂ := b22e32 X0
                   grind)
                | exact superpose b22e32 b22e15
                | exact resolve b22e15 b22e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e48 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e15 (M.op X0 X0) X1 X2
                   have i₂ := b22e34 X0 X0
                   grind)
                | exact superpose b22e34 b22e15
                | exact resolve b22e15 b22e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e53 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b22e19 (σ x) X0
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) X0
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b22e19 X0 X0
                   have i₂ := b22e20 X0 X1
                   grind)
                | (have i₁ := b22e19 X0 X1
                   have i₂ := b22e20 X0 X1
                   grind)
                | exact superpose b22e20 b22e19
                | (have j0 := b22e19 X0 X0
                   have j1 := b22e20 X0 X1
                   grind)
                | (have r₁ := b22e19 X0 X1
                   have r₂ := b22e20 X0 X1
                   grind)
                | (have r₁ := b22e19 X1 X1
                   have r₂ := b22e20 X1 X1
                   grind)
                | exact resolve b22e19 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e101 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b22e20 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e102 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b22e94 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e94
              have b22e106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                first
                | (have j0 := b22e102 X0 X1
                   have j1 := b22e101 X0 X1
                   grind)
                | (have r₁ := b22e102 X0 X1
                   have r₂ := b22e101 X0 X1
                   grind)
                | (have r₁ := b22e102 X0 X0
                   have r₂ := b22e101 X0 X1
                   grind)
                | exact resolve b22e102 b22e101
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e101 b22e102
              have b22e415 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e31 X1 X0 (M.op X0 X1) X2
                   have i₂ := b22e34 (M.op X0 X1) (M.op X0 X1)
                   grind)
                | exact superpose b22e34 b22e31
                | exact resolve b22e31 b22e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e420 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) X2) = (M.op (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e31 (M.op X0 X0) X1 X2 X0
                   have i₂ := b22e32 X0
                   grind)
                | exact superpose b22e32 b22e31
                | exact resolve b22e31 b22e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e32
              have b22e436 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X3) = (M.op (M.op (M.op X1 X3) (M.op X1 X3)) (M.op (M.op (M.op X0 X1) X2) X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b22e15 (M.op X1 X3) (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X4
                   have i₂ := b22e31 X1 X0 X2 X3
                   grind)
                | exact superpose b22e31 b22e15
                | exact resolve b22e15 b22e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e31
              have b22e776 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b22e53 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e53
              have b22e780 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e776
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e776 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e776
              have b22e784 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b22e780
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e780
                | exact resolve b22e780 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e780
              have b22e996 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ y) (σ y)
                   have i₂ := b22e784
                   grind)
                | exact superpose b22e784 b22e19
                | exact resolve b22e19 b22e784
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e999 : (σ y) = (M.op (σ (k x y)) (σ (k x y))) := by
                first
                | (have i₁ := b22e34 (σ y) (σ y)
                   have i₂ := b22e784
                   grind)
                | exact superpose b22e784 b22e34
                | exact resolve b22e34 b22e784
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e1004 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by grind
              clear b22e996
              have b22e1007 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e1004
                   have i₂ := b22e21 y y
                   grind)
                | exact superpose b22e21 b22e1004
                | exact resolve b22e1004 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e1004
              have b22e2593 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b22e999
                   have i₂ := b22e20 x y
                   grind)
                | exact superpose b22e20 b22e999
                | (have j1 := b22e20 x y
                   grind)
                | exact resolve b22e999 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e999
              have b22e2643 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b22e2593
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e2593 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2593
              have b22e2648 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
                first
                | (have r₁ := b22e2643
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e2643 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2643
              have b22e3589 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b22e34 (σ (M.op x y)) (σ (M.op x y))
                   have i₂ := b22e2648
                   grind)
                | exact superpose b22e2648 b22e34
                | exact resolve b22e34 b22e2648
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2648
              have b22e3838 : (σ (M.op x y)) = (σ (k x y)) := by
                first
                | (have i₁ := b22e784
                   have i₂ := b22e3589
                   grind)
                | exact superpose b22e3589 b22e784
                | exact resolve b22e784 b22e3589
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e784 b22e3589
              have b22e3958 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X1 X0) X2) X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e436 X1 X0 X2 X0 X3
                   have i₂ := b22e34 X0 X0
                   grind)
                | exact superpose b22e34 b22e436
                | exact resolve b22e436 b22e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e436
              have b22e4194 : (k x y) = (τ (σ (M.op x y))) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e3838
                   grind)
                | exact superpose b22e3838 b22e16
                | exact resolve b22e16 b22e3838
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e4227 : (M.op x y) = (k x y) := by
                first
                | (have i₁ := b22e4194
                   have i₂ := b22e16 (M.op x y)
                   grind)
                | exact superpose b22e16 b22e4194
                | exact resolve b22e4194 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e4194
              have b22e7096 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b22e48 X0 (M.op X0 X0) X1
                   have i₂ := b22e34 X0 X0
                   grind)
                | exact superpose b22e34 b22e48
                | exact resolve b22e48 b22e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e7864 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b22e3958 X1 X0 (M.op X0 X1) (M.op (M.op x (M.op X0 X1)) x)
                   have i₂ := b22e15 (M.op X0 X1) x x
                   grind)
                | exact superpose b22e15 b22e3958
                | exact resolve b22e3958 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3958
              have b22e8165 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b22e7864 (M.op X0 X0) (M.op X0 X1)
                   have i₂ := b22e34 X0 X1
                   grind)
                | exact superpose b22e34 b22e7864
                | exact resolve b22e7864 b22e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e13219 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
                intro X0 X1
                first
                | (have i₁ := b22e420 X1 (M.op X1 X1) x
                   have i₂ := b22e34 X1 X1
                   grind)
                | exact superpose b22e34 b22e420
                | exact resolve b22e420 b22e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e420
              have b22e13433 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X0) X0) := by
                intro X0 X1
                first
                | (have i₁ := b22e13219 X0 X1
                   have i₂ := b22e8165 X0 X1
                   grind)
                | exact superpose b22e8165 b22e13219
                | exact resolve b22e13219 b22e8165
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e13219
              have b22e13611 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e15 X0 (M.op (M.op X0 X1) X0) X2
                   have i₂ := b22e13433 X0 X1
                   grind)
                | exact superpose b22e13433 b22e15
                | exact resolve b22e15 b22e13433
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e13433
              have b22e14505 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e48 (M.op X0 X1) (M.op X0 X0) X2
                   have i₂ := b22e13611 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b22e13611 b22e48
                | exact resolve b22e48 b22e13611
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e48 b22e13611
              have b22e14592 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X1) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e14505 X0 X1 X2
                   have i₂ := b22e8165 X0 X1
                   grind)
                | exact superpose b22e8165 b22e14505
                | exact resolve b22e14505 b22e8165
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e8165 b22e14505
              have b22e40694 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e14592 X0 X1 X1
                   have i₂ := b22e415 X0 X1 X2
                   grind)
                | (have i₁ := b22e14592 X1 X1 X2
                   have i₂ := b22e415 X1 X1 X2
                   grind)
                | exact superpose b22e415 b22e14592
                | exact resolve b22e14592 b22e415
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e415 b22e14592
              have b22e129851 : (k x y) = (τ (σ (k y y))) ∨ (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e1007
                   grind)
                | exact superpose b22e1007 b22e16
                | exact resolve b22e16 b22e1007
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e1007
              have b22e129886 : (k x y) = (k y y) ∨ (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e129851
                   have i₂ := b22e16 (k y y)
                   grind)
                | exact superpose b22e16 b22e129851
                | exact resolve b22e129851 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e129851
              have b22e129912 : (M.op x y) = (k y y) ∨ (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e129886
                   have i₂ := b22e4227
                   grind)
                | exact superpose b22e4227 b22e129886
                | exact resolve b22e129886 b22e4227
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e4227 b22e129886
              have b22e129930 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k y y) := by
                first
                | (have i₁ := b22e129912
                   have i₂ := b22e3838
                   grind)
                | exact superpose b22e3838 b22e129912
                | exact resolve b22e129912 b22e3838
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3838 b22e129912
              have b22e131511 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k y y) := by
                first
                | (have i₁ := b22e16 (M.op x y)
                   have i₂ := b22e129930
                   grind)
                | exact superpose b22e129930 b22e16
                | exact resolve b22e16 b22e129930
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e129930
              have b22e131547 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b22e131511
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e131511
                | exact resolve b22e131511 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e131511
              have b22e132143 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b22e106 y y
                   have i₂ := b22e131547
                   grind)
                | exact superpose b22e131547 b22e106
                | (have j0 := b22e106 y y
                   grind)
                | exact resolve b22e106 b22e131547
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e106 b22e131547
              have b22e132151 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
              clear b22e132143
              have b22e132157 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
                first
                | (have r₁ := b22e132151
                   have r₂ := b22e27
                   grind)
                | exact resolve b22e132151 b22e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e132151
              have b22e132457 : ∀ X0 : G, (M.op (M.op y y) x) = (M.op (M.op y y) (M.op y X0)) ∨ y = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b22e40694 x y x
                   have i₂ := b22e132157
                   grind)
                | exact superpose b22e132157 b22e40694
                | exact resolve b22e40694 b22e132157
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e40694 b22e132157
              have b22e132490 : y = (M.op (M.op y y) x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b22e132457 x
                   have i₂ := b22e34 y x
                   grind)
                | exact superpose b22e34 b22e132457
                | exact resolve b22e132457 b22e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e34 b22e132457
              have b22e149106 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b22e7864 (M.op y y) x
                   have i₂ := b22e132490
                   grind)
                | exact superpose b22e132490 b22e7864
                | exact resolve b22e7864 b22e132490
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e7864 b22e132490
              have b22e149241 : y = (M.op x y) := by
                first
                | (have r₁ := b22e149106
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e149106 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e149106
              have b22e150252 : (M.op x y) = (M.op x x) := by
                first
                | (have i₁ := b22e7096 x y
                   have i₂ := b22e149241
                   grind)
                | exact superpose b22e149241 b22e7096
                | exact resolve b22e7096 b22e149241
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e7096 b22e149241
              have b22e150335 : False := by grind
              exact b22e150335
            · have b23e28 : (M.op y y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : False := by grind
              exact b23e29
        · rcases eq_or_ne (M.op y y) (y) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : x ≠ (M.op x y) := by grind
            have b24e23 : (M.op x y) ≠ (M.op x x) := by grind
            have b24e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X0 X1
                 have i₂ := b24e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e775 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e25
                 have i₂ := b24e64 x y
                 grind)
              | exact superpose b24e64 b24e25
              | (have j1 := b24e64 x y
                 grind)
              | (have r₁ := b24e25
                 have r₂ := b24e64 x y
                 grind)
              | exact resolve b24e25 b24e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e64
            have b24e839 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
            clear b24e775
            have b24e846 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b24e839
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e839 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e839
            have b24e863 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e846
                 grind)
              | exact superpose b24e846 b24e21
              | exact resolve b24e21 b24e846
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e846
            have b24e1304 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b24e863
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e863
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e863 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e863
            have b24e1305 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
            clear b24e1304
            have b24e1309 : x = (M.op x y) := by
              first
              | (have r₁ := b24e1305
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e1305 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1305
            have b24e1314 : False := by grind
            exact b24e1314
          · rcases eq_or_ne (M.op y y) (M.op y y) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : x ≠ (M.op x y) := by grind
              have b25e24 : (M.op x y) ≠ (M.op x x) := by grind
              have b25e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e26 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e79 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b25e26
                   have i₂ := b25e20 (σ x) X0
                   grind)
                | (have i₁ := b25e26
                   have i₂ := b25e20 (σ x) (σ x)
                   grind)
                | exact superpose b25e20 b25e26
                | (have j1 := b25e20 (σ x) X0
                   grind)
                | (have r₁ := b25e26
                   have r₂ := b25e20 (σ x) (σ y)
                   grind)
                | exact resolve b25e26 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e1092 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b25e79 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e79
              have b25e1094 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b25e1092
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e1092 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1092
              have b25e1096 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b25e1094
                   have i₂ := b25e21 x y
                   grind)
                | exact superpose b25e21 b25e1094
                | exact resolve b25e1094 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1094
              have b25e1101 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e1096
                   grind)
                | exact superpose b25e1096 b25e22
                | exact resolve b25e22 b25e1096
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1096
              have b25e1710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b25e1101
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e1101
                | (have j1 := b25e20 x y
                   grind)
                | exact resolve b25e1101 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1101
              have b25e1711 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
              clear b25e1710
              have b25e1715 : x = (M.op x y) := by
                first
                | (have r₁ := b25e1711
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e1711 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1711
              have b25e1719 : False := by grind
              exact b25e1719
            · have b26e28 : (M.op y y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e29 : False := by grind
              exact b26e29
