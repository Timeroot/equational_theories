import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation727 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law727 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
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
      have b0e40 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e41 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e43 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e41
      have b0e44 : (M.op x x) = (k x y) := by grind
      clear b0e40
      have b0e45 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e43
        | exact resolve b0e43 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e46 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e44
           grind)
        | exact superpose b0e44 b0e45
        | exact resolve b0e45 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e45
      have b0e66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X0 X0) (M.op X1 X0)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e66 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e165 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e69 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e168 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e165 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e165 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e165 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e165 X0 X1
           have r₂ := b0e16 (M.op X0 X0) (M.op X1 X0)
           grind)
        | exact resolve b0e165 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e165
      have b0e288 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e168 X1 (τ X0)
           grind)
        | exact superpose b0e168 b0e23
        | (have j1 := b0e168 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e168 (σ X1) (σ X0)
           grind)
        | exact superpose b0e168 b0e17
        | (have j1 := b0e168 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e168
      have b0e3411 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e288 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e288
        | exact resolve b0e288 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e288
      have b0e3457 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e3411 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e3411
        | (have j0 := b0e3411 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e3411 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3411
      have b0e17559 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e289 x y
           grind)
        | exact superpose b0e289 b0e18
        | (have j1 := b0e289 x y
           grind)
        | exact resolve b0e18 b0e289
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e289
      have b0e18223 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e17559
           have i₂ := b0e3457 x y
           grind)
        | exact superpose b0e3457 b0e17559
        | (have j1 := b0e3457 (σ x) (σ y)
           grind)
        | (have r₁ := b0e17559
           have r₂ := b0e3457 x y
           grind)
        | (have r₁ := b0e17559
           have r₂ := b0e3457 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e17559
           have r₂ := b0e3457 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e17559 b0e3457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3457 b0e17559
      have b0e18224 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e18223
      have b0e20151 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e18224
           grind)
        | exact superpose b0e18224 b0e12
        | exact resolve b0e12 b0e18224
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18224
      have b0e20204 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e20151
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e20151
        | exact resolve b0e20151 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20151
      have b0e20205 : x = y := by grind
      clear b0e20204
      have b0e21784 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20205
           grind)
        | exact superpose b0e20205 b0e18
        | exact resolve b0e18 b0e20205
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20205
      have b0e21793 : False := by grind
      exact b0e21793
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op x x) = (k x y) := by grind
        clear b2e49
        have b2e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e50 (σ X0)
             grind)
          | exact superpose b2e50 b2e18
          | exact resolve b2e18 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e53 X0
             have i₂ := b2e50 X0
             grind)
          | exact superpose b2e50 b2e53
          | exact resolve b2e53 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e53
        have b2e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e68 X0 X1
             have i₂ := b2e60 X1
             grind)
          | exact superpose b2e60 b2e68
          | (have j0 := b2e68 X0 X1
             grind)
          | exact resolve b2e68 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e349 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e82 y x
             grind)
          | exact superpose b2e82 b2e21
          | (have j1 := b2e82 y x
             grind)
          | exact resolve b2e21 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e384 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e349
             have r₂ := b2e22
             grind)
          | exact resolve b2e349 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e349
        have b2e398 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e384
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e384
          | exact resolve b2e384 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e384
        have b2e404 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e398
             have r₂ := b2e60 x
             grind)
          | exact resolve b2e398 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e398
        have b2e408 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e404
             grind)
          | exact superpose b2e404 b2e21
          | exact resolve b2e21 b2e404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e404
        have b2e417 : False := by grind
        exact b2e417
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e51 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e49
        have b6e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e51
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e51
          | exact resolve b6e51 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e86 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e52
             grind)
          | exact superpose b6e52 b6e15
          | exact resolve b6e15 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e90 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e86
        have b6e91 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e90
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e90
          | exact resolve b6e90 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e92 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e91
             have i₂ := b6e50 x
             grind)
          | exact superpose b6e50 b6e91
          | exact resolve b6e91 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50 b6e91
        have b6e119 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e92
             grind)
          | exact superpose b6e92 b6e13
          | exact resolve b6e13 b6e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e120 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e119
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e119
          | exact resolve b6e119 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e119
        have b6e166 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e120
             grind)
          | exact superpose b6e120 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e167 : (M.op x x) = (M.op y x) ∨ x = y := by grind
        clear b6e166
        have b6e169 : x = y := by
          first
          | (have r₁ := b6e167
             have r₂ := b6e20
             grind)
          | exact resolve b6e167 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e167
        have b6e172 : False := by grind
        exact b6e172
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e27 X1 X0
               grind)
            | exact superpose b8e27 b8e14
            | exact resolve b8e14 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e42 (σ X0)
               grind)
            | exact superpose b8e42 b8e19
            | exact resolve b8e19 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e44
            | exact resolve b8e44 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e44
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X1 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e55 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e55
            | (have j0 := b8e55 X0 X1
               grind)
            | exact resolve b8e55 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e55
          have b8e144 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e65 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e147 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e144 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e144 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e144 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e144 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X1 X0)
               grind)
            | exact resolve b8e144 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144
          have b8e252 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e39 X1 X0
               have i₂ := b8e147 (σ X1) X0
               grind)
            | exact superpose b8e147 b8e39
            | (have j1 := b8e147 (k X1 (τ X0)) (τ (M.op X0 (σ X1)))
               grind)
            | exact resolve b8e39 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e333 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e68 x y
               grind)
            | exact superpose b8e68 b8e20
            | (have j1 := b8e68 x y
               grind)
            | exact resolve b8e20 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e370 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e333
               have r₂ := b8e24
               grind)
            | exact resolve b8e333 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e333
          have b8e2118 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have i₁ := b8e370
               have i₂ := b8e147 y x
               grind)
            | exact superpose b8e147 b8e370
            | (have j1 := b8e147 (M.op (σ x) (σ y)) (σ (M.op y y))
               grind)
            | (have r₁ := b8e370
               have r₂ := b8e147 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e370
               have r₂ := b8e147 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e370 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147 b8e370
          have b8e2122 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by grind
          clear b8e2118
          have b8e2126 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e2122
               have r₂ := b8e22
               grind)
            | exact resolve b8e2122 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2122
          have b8e2130 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2126
               grind)
            | exact superpose b8e2126 b8e20
            | exact resolve b8e20 b8e2126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2131 : (k y (τ (σ x))) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e252 (σ x) y
               have i₂ := b8e2126
               grind)
            | exact superpose b8e2126 b8e252
            | (have j0 := b8e252 (σ y) x
               grind)
            | exact resolve b8e252 b8e2126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e252 b8e2126
          have b8e2154 : (k y (τ (σ x))) = (τ (σ (M.op y y))) := by
            first
            | (have r₁ := b8e2131
               have r₂ := b8e24
               grind)
            | exact resolve b8e2131 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2131
          have b8e2157 : (M.op y y) = (k y (τ (σ x))) := by
            first
            | (have i₁ := b8e2154
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e2154
            | exact resolve b8e2154 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2154
          have b8e2159 : (k y x) = (M.op y y) := by
            first
            | (have i₁ := b8e2157
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e2157
            | exact resolve b8e2157 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2157
          have b8e2177 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e18 y x
               have i₂ := b8e2159
               grind)
            | exact superpose b8e2159 b8e18
            | (have j0 := b8e18 y x
               grind)
            | exact resolve b8e18 b8e2159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2159
          have b8e2178 : (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b8e2177
          have b8e2180 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e2178
               have r₂ := b8e22
               grind)
            | exact resolve b8e2178 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2178
          have b8e2575 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e2130
               have i₂ := b8e2180
               grind)
            | exact superpose b8e2180 b8e2130
            | exact resolve b8e2130 b8e2180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2130 b8e2180
          have b8e2576 : False := by grind
          exact b8e2576

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation727 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law727 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e27 : ∀ X0 : G, (M.op y (M.op y (M.op y X0))) = X0 := by
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
      have b0e28 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) = X0 := by
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
      have b0e33 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 (M.op (M.op X1 y) X0)
           have i₂ := b0e11 X0 y X1
           grind)
        | exact superpose b0e11 b0e27
        | exact resolve b0e27 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e36 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 y
           grind)
        | (have r₁ := b0e14 X0 y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ y)
           grind)
        | (have r₁ := b0e14 X0 (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b0e37 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e39 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
        intro X0
        first
        | (have j0 := b0e36 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e45 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 y
           have i₂ := b0e38 (σ X0)
           grind)
        | exact superpose b0e38 b0e17
        | exact resolve b0e17 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e47 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e45 X0
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e45
        | exact resolve b0e45 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e45
      have b0e53 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
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
      have b0e55 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e53 X0 X2 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e100 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ y)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (M.op (M.op X1 (σ y)) X0)
           have i₂ := b0e11 X0 (σ y) X1
           grind)
        | exact superpose b0e11 b0e28
        | exact resolve b0e28 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e186 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e55 X1 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e187 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e186 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186
      have b0e737 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e187 (σ X1) (σ X0)
           grind)
        | exact superpose b0e187 b0e17
        | (have j1 := b0e187 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e739 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e187 (τ X1) X0
           grind)
        | exact superpose b0e187 b0e21
        | (have j1 := b0e187 (τ X1) X0
           grind)
        | exact resolve b0e21 b0e187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e187
      have b0e52562 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e739 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e739
        | exact resolve b0e739 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e739
      have b0e52733 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e52562 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e52562
        | (have j0 := b0e52562 X0 X1
           grind)
        | exact resolve b0e52562 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52562
      have b0e72258 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e737 x y
           grind)
        | exact superpose b0e737 b0e18
        | (have j1 := b0e737 x y
           grind)
        | exact resolve b0e18 b0e737
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e737
      have b0e593469 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e72258
           have i₂ := b0e52733 y x
           grind)
        | exact superpose b0e52733 b0e72258
        | (have j1 := b0e52733 (σ y) (σ x)
           grind)
        | (have r₁ := b0e72258
           have r₂ := b0e52733 y x
           grind)
        | exact resolve b0e72258 b0e52733
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52733 b0e72258
      have b0e593470 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e593469
      have b0e594335 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e100 X0 (σ x)
           have i₂ := b0e593470
           grind)
        | exact superpose b0e593470 b0e100
        | exact resolve b0e100 b0e593470
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100
      have b0e596092 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e593470
           have i₂ := b0e594335 (σ y)
           grind)
        | exact superpose b0e594335 b0e593470
        | exact resolve b0e593470 b0e594335
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e593470 b0e594335
      have b0e596491 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e596092
      have b0e596554 : x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e596491
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e596491
        | exact resolve b0e596491 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e596491
      have b0e597738 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e33 X0 x
           have i₂ := b0e596554
           grind)
        | exact superpose b0e596554 b0e33
        | exact resolve b0e33 b0e596554
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e600753 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e596554
           have i₂ := b0e597738 y
           grind)
        | exact superpose b0e597738 b0e596554
        | exact resolve b0e596554 b0e597738
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e596554 b0e597738
      have b0e601336 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
      clear b0e600753
      have b0e601479 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e601336
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e601336
        | exact resolve b0e601336 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e601336
      have b0e601849 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e601479
           grind)
        | exact superpose b0e601479 b0e12
        | exact resolve b0e12 b0e601479
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e601479
      have b0e602029 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e601849
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e601849
        | exact resolve b0e601849 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e601849
      have b0e602030 : x = y := by grind
      clear b0e602029
      have b0e606071 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e602030
           grind)
        | exact superpose b0e602030 b0e18
        | exact resolve b0e18 b0e602030
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e602030
      have b0e606077 : False := by grind
      exact b0e606077
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 : G, (M.op y (M.op y (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
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
        have b1e35 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e37 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e39 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e37
        have b1e40 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e39
             have r₂ := b1e21
             grind)
          | exact resolve b1e39 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e41 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e40
          | exact resolve b1e40 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e35 x
             grind)
          | exact superpose b1e35 b1e41
          | exact resolve b1e41 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e41
        have b1e45 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e42
             grind)
          | exact superpose b1e42 b1e13
          | exact resolve b1e13 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e46 : y = (M.op y x) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e45
          | exact resolve b1e45 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e59 : x = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b1e25 x
             have i₂ := b1e46
             grind)
          | exact superpose b1e46 b1e25
          | exact resolve b1e25 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e46
        have b1e63 : x = (M.op y y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e59
          | exact resolve b1e59 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e64 : x = y := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e63
          | exact resolve b1e63 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e74 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e22
          | exact resolve b1e22 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e75 : False := by grind
        exact b1e75
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e33 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
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
        have b2e34 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e33 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e482 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e52 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e484 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e482 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482
        have b2e1193 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e484 y
             have i₂ := b2e34 y
             grind)
          | exact superpose b2e34 b2e484
          | (have j0 := b2e484 y
             grind)
          | exact resolve b2e484 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e484
        have b2e1202 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have r₁ := b2e1193
             have r₂ := b2e21
             grind)
          | exact resolve b2e1193 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1193
        have b2e1207 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1202
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1202
          | exact resolve b2e1202 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1202
        have b2e1208 : False := by grind
        exact b2e1208
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e32 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b3e33 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e53 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e33 (σ X0)
             grind)
          | exact superpose b3e33 b3e18
          | exact resolve b3e18 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e81 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e22
          | exact resolve b3e22 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e120 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e81
             grind)
          | exact superpose b3e81 b3e13
          | exact resolve b3e13 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e122 : y = (k y y) := by
          first
          | (have i₁ := b3e120
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e120
          | exact resolve b3e120 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120
        have b3e130 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e122
             grind)
          | exact superpose b3e122 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e122
        have b3e131 : y = (M.op y y) := by grind
        clear b3e130
        have b3e133 : False := by grind
        exact b3e133
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e31 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
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
          have b4e32 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
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
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
               have i₂ := b4e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e31 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e31
            | exact resolve b4e31 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (M.op y (M.op (M.op X1 y) X0)) = (M.op x (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 (M.op y (M.op (M.op X1 y) X0))
               have i₂ := b4e13 X0 y X1
               grind)
            | exact superpose b4e13 b4e31
            | exact resolve b4e31 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : x ≠ x ∨ x = (M.op x x) ∨ x = (k (M.op x y) x) := by
            first
            | (have i₁ := b4e17 (M.op x y) x
               have i₂ := b4e35
               grind)
            | exact superpose b4e35 b4e17
            | (have j0 := b4e17 (M.op x y) x
               grind)
            | (have r₁ := b4e17 (M.op x y) x
               have r₂ := b4e35
               grind)
            | exact resolve b4e17 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by grind
          clear b4e42
          have b4e56 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X2 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e56 X0 X2 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e72 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e32 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e113 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3)) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op (M.op X2 X1) X0) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e34 X3 (M.op (M.op X2 X1) X0) X1 X1
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e123 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X2 X0) x
               have i₂ := b4e34 X1 X0 X2 x
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e169 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e60 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e170 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e169 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169
          have b4e192 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b4e123 x (M.op x y) X0
               have i₂ := b4e35
               grind)
            | exact superpose b4e35 b4e123
            | exact resolve b4e123 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e193 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e123 y x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e123
            | exact resolve b4e123 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e194 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e123 X2 (M.op (M.op X3 X2) X0) X1
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e123
            | exact resolve b4e123 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e196 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e123 (σ x) (σ y) X0
               have i₂ := b4e72
               grind)
            | exact superpose b4e72 b4e123
            | exact resolve b4e123 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e197 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e123 x (M.op y X0) X1
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e123
            | exact resolve b4e123 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e205 : (M.op x y) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b4e192 x
               have i₂ := b4e197 (M.op x x) x
               grind)
            | exact superpose b4e197 b4e192
            | exact resolve b4e192 b4e197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e192
          have b4e576 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e170 (σ X1) (σ X0)
               grind)
            | exact superpose b4e170 b4e19
            | (have j1 := b4e170 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e170
          have b4e746 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e194 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
               have i₂ := b4e123 X2 X0 x
               grind)
            | exact superpose b4e123 b4e194
            | exact resolve b4e194 b4e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123
          have b4e748 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 (M.op y y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e194 X1 X0 (M.op y y) (M.op x y)
               have i₂ := b4e193 x
               grind)
            | exact superpose b4e193 b4e194
            | exact resolve b4e194 b4e193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193
          have b4e761 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 y) X0)) X3) = (M.op (M.op x (M.op x X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e194 X3 X1 (M.op (M.op X2 y) X0) y
               have i₂ := b4e36 X0 X2
               grind)
            | exact superpose b4e36 b4e194
            | exact resolve b4e194 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e1106 : ∀ X0 X2 : G, (M.op (M.op (M.op y y) (M.op x X0)) (M.op (M.op (M.op y y) (M.op x X0)) (M.op X0 X2))) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b4e33 x (M.op y y) X0 x
               have i₂ := b4e748 X0 x
               grind)
            | exact superpose b4e748 b4e33
            | exact resolve b4e33 b4e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e748
          have b4e1149 : ∀ X0 X2 : G, (M.op (M.op y (M.op (M.op y y) (M.op x X0))) (M.op (M.op x X0) (M.op X0 X2))) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b4e1106 X0 X2
               have i₂ := b4e113 (M.op x X0) y y (M.op X0 X2)
               grind)
            | exact superpose b4e113 b4e1106
            | exact resolve b4e1106 b4e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113 b4e1106
          have b4e1153 : ∀ X0 X2 : G, (M.op (M.op x (M.op x (M.op x X0))) (M.op (M.op x X0) (M.op X0 X2))) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b4e1149 X0 X2
               have i₂ := b4e761 (M.op x X0) y y (M.op (M.op x X0) (M.op X0 X2))
               grind)
            | exact superpose b4e761 b4e1149
            | exact resolve b4e1149 b4e761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e761 b4e1149
          have b4e1155 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x X0) (M.op X0 X2))) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b4e1153 X0 X2
               have i₂ := b4e746 X0 x x (M.op (M.op x X0) (M.op X0 X2))
               grind)
            | exact superpose b4e746 b4e1153
            | exact resolve b4e1153 b4e746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e746 b4e1153
          have b4e1439 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1155 X1 X2
               have i₂ := b4e194 (M.op X1 X2) x X1 X0
               grind)
            | (have i₁ := b4e1155 X1 X2
               have i₂ := b4e194 (M.op X1 X2) X0 X1 x
               grind)
            | exact superpose b4e194 b4e1155
            | exact resolve b4e1155 b4e194
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194 b4e1155
          have b4e112582 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e576 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e576
          have b4e122847 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e112582 x (M.op x y)
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e112582
            | (have j0 := b4e112582 x (M.op x y)
               grind)
            | exact resolve b4e112582 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e112582
          have b4e122870 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
          clear b4e122847
          have b4e182088 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b4e1439 X0 (σ x) (σ (M.op x y))
               have i₂ := b4e122870
               grind)
            | exact superpose b4e122870 b4e1439
            | exact resolve b4e1439 b4e122870
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1439 b4e122870
          have b4e182147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e182088 x
               have i₂ := b4e196 x
               grind)
            | exact superpose b4e196 b4e182088
            | exact resolve b4e182088 b4e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196 b4e182088
          have b4e182207 : x = (M.op x x) := by
            first
            | (have r₁ := b4e182147
               have r₂ := b4e20
               grind)
            | exact resolve b4e182147 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182147
          have b4e186381 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e205
               have i₂ := b4e182207
               grind)
            | exact superpose b4e182207 b4e205
            | exact resolve b4e205 b4e182207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e205
          have b4e186415 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e197 X0 x
               have i₂ := b4e182207
               grind)
            | exact superpose b4e182207 b4e197
            | exact resolve b4e197 b4e182207
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e197 b4e182207
          have b4e186640 : y = (M.op x y) := by
            first
            | (have i₁ := b4e186381
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e186381
            | exact resolve b4e186381 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186381
          have b4e186717 : y = (M.op y y) := by
            first
            | (have i₁ := b4e186640
               have i₂ := b4e186415 y
               grind)
            | exact superpose b4e186415 b4e186640
            | exact resolve b4e186640 b4e186415
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186415 b4e186640
          have b4e186775 : False := by grind
          exact b4e186775
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b5e38 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e43 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e38
          have b5e44 : y = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e366 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e47 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e7327 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e366 y x
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e366
            | (have j0 := b5e366 y y
               grind)
            | exact resolve b5e366 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e366
          have b5e7330 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e7327
          have b5e7335 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e7330
               have r₂ := b5e23
               grind)
            | exact resolve b5e7330 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7330
          have b5e7338 : False := by grind
          exact b5e7338
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e32 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b6e33 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e32 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e35 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e33 (σ X0)
             grind)
          | exact superpose b6e33 b6e18
          | exact resolve b6e18 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e76 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e35 y
             grind)
          | exact superpose b6e35 b6e22
          | exact resolve b6e22 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e111 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e13
          | exact resolve b6e13 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e113 : y = (k y y) := by
          first
          | (have i₁ := b6e111
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e111
          | exact resolve b6e111 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111
        have b6e122 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e113
             grind)
          | exact superpose b6e113 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e113
        have b6e123 : y = (M.op y y) := by grind
        clear b6e122
        have b6e125 : False := by grind
        exact b6e125
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
          have b7e50 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e52 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e50
          have b7e53 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e52
               have r₂ := b7e23
               grind)
            | exact resolve b7e52 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e54 : (σ y) = (σ (k x y)) := by
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
          have b7e58 : (k x y) = (τ (σ y)) := by
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
          have b7e59 : y = (k x y) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e58
            | exact resolve b7e58 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e78 : y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e59
               grind)
            | exact superpose b7e59 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e79 : y = (M.op y x) ∨ y = (M.op y y) := by grind
          clear b7e78
          have b7e81 : y = (M.op y y) := by
            first
            | (have r₁ := b7e79
               have r₂ := b7e22
               grind)
            | exact resolve b7e79 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e83 : False := by grind
          exact b7e83
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e25 X0 X1
               grind)
            | exact superpose b8e25 b8e14
            | exact resolve b8e14 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
               have i₂ := b8e13 X0 (M.op X2 X1) X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e30
            | exact resolve b8e30 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X2 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 X2 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e69 X0 X2 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e111 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X0 X3)) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op (M.op X2 X1) X0) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e32 X3 (M.op (M.op X2 X1) X0) X1 X1
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X1) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X3 (M.op X2 X0)) X1) X0 X2
               have i₂ := b8e32 X1 X0 X2 X3
               grind)
            | exact superpose b8e32 b8e13
            | exact resolve b8e13 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e118 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 (M.op X2 X0) x
               have i₂ := b8e32 X1 X0 X2 x
               grind)
            | exact superpose b8e32 b8e13
            | exact resolve b8e13 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e132 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e118 (M.op X2 X3) (M.op X3 (M.op X3 X0)) X1
               have i₂ := b8e118 X3 X0 X2
               grind)
            | exact superpose b8e118 b8e118
            | exact resolve b8e118 b8e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e118 X2 (M.op (M.op X3 X2) X0) X1
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e118
            | exact resolve b8e118 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e159 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op (M.op X3 (M.op X4 X0)) X1)) X5) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e133 X5 X2 (M.op (M.op X3 (M.op X4 X0)) X1) (M.op X4 X0)
               have i₂ := b8e32 X1 X0 X4 X3
               grind)
            | exact superpose b8e32 b8e133
            | exact resolve b8e133 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e160 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e133 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
               have i₂ := b8e118 X2 X0 x
               grind)
            | exact superpose b8e118 b8e133
            | exact resolve b8e133 b8e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e232 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e233 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e232 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e232
          have b8e238 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e233 (σ X1) (σ X0)
               grind)
            | exact superpose b8e233 b8e19
            | (have j1 := b8e233 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e241 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e233 (τ X1) X0
               grind)
            | exact superpose b8e233 b8e25
            | (have j1 := b8e233 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e281 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op (M.op X2 X1) X3)) (M.op X3 X0)) (M.op (M.op (M.op X1 (M.op (M.op X2 X1) X3)) (M.op X3 X0)) (M.op X0 X4))) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X4 (M.op (M.op X1 (M.op (M.op X2 X1) X3)) (M.op X3 X0)) (M.op X1 (M.op (M.op X2 X1) X3))
               have i₂ := b8e31 X3 X1 X2 X0
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e291 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X2 X1) X3) (M.op (M.op X1 (M.op (M.op X2 X1) X3)) (M.op X3 X0))) (M.op (M.op X3 X0) (M.op X0 X4))) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e281 X0 X1 X2 X3 X4
               have i₂ := b8e111 (M.op X3 X0) (M.op (M.op X2 X1) X3) X1 (M.op X0 X4)
               grind)
            | exact superpose b8e111 b8e281
            | exact resolve b8e281 b8e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111 b8e281
          have b8e305 : ∀ X0 X3 X4 : G, (M.op (M.op X3 (M.op X3 (M.op X3 X0))) (M.op (M.op X3 X0) (M.op X0 X4))) = X4 := by
            intro X0 X3 X4
            first
            | (have i₁ := b8e291 X0 x x X3 X4
               have i₂ := b8e159 X3 (M.op X3 X0) (M.op (M.op x x) X3) x (M.op x x) (M.op (M.op X3 X0) (M.op X0 X4))
               grind)
            | exact superpose b8e159 b8e291
            | exact resolve b8e291 b8e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159 b8e291
          have b8e315 : ∀ X0 X3 X4 : G, (M.op X0 (M.op (M.op X3 X0) (M.op X0 X4))) = X4 := by
            intro X0 X3 X4
            first
            | (have i₁ := b8e305 X0 X3 X4
               have i₂ := b8e160 X0 X3 X3 (M.op (M.op X3 X0) (M.op X0 X4))
               grind)
            | exact superpose b8e160 b8e305
            | exact resolve b8e305 b8e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160 b8e305
          have b8e1201 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X4 X3) X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e117 X3 (M.op (M.op X4 X3) X0) X2 X1
               have i₂ := b8e13 X0 X3 X4
               grind)
            | exact superpose b8e13 b8e117
            | exact resolve b8e117 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e19971 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e241 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e241
            | exact resolve b8e241 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e241
          have b8e20048 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e19971 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e19971
            | (have j0 := b8e19971 X0 X1
               grind)
            | exact resolve b8e19971 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19971
          have b8e24402 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e238 x y
               grind)
            | exact superpose b8e238 b8e20
            | (have j1 := b8e238 x y
               grind)
            | exact resolve b8e20 b8e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e24498 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e238 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29547 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24498 (τ X1) (τ X0)
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e24498
            | (have j0 := b8e24498 (τ X1) (τ X0)
               grind)
            | exact resolve b8e24498 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41
          have b8e29587 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e29547 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e29547
            | (have j0 := b8e29547 X0 X1
               grind)
            | exact resolve b8e29547 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29547
          have b8e29591 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e29587 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e29587
            | (have j0 := b8e29587 X0 X1
               grind)
            | exact resolve b8e29587 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29587
          have b8e29594 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e29591 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e29591
            | (have j0 := b8e29591 X0 X1
               grind)
            | exact resolve b8e29591 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29591
          have b8e29595 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e29594 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e29594
            | (have j0 := b8e29594 X0 X1
               grind)
            | exact resolve b8e29594 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29594
          have b8e69985 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e24402
               have i₂ := b8e20048 y x
               grind)
            | exact superpose b8e20048 b8e24402
            | (have j1 := b8e20048 (σ y) (σ x)
               grind)
            | (have r₁ := b8e24402
               have r₂ := b8e20048 y x
               grind)
            | exact resolve b8e24402 b8e20048
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20048 b8e24402
          have b8e69986 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e69985
          have b8e71354 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 (σ y) (σ x)
               have i₂ := b8e69986
               grind)
            | exact superpose b8e69986 b8e13
            | exact resolve b8e13 b8e69986
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e109492 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e71354 (σ y)
               have i₂ := b8e69986
               grind)
            | exact superpose b8e69986 b8e71354
            | exact resolve b8e71354 b8e69986
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69986 b8e71354
          have b8e109729 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
          clear b8e109492
          have b8e110530 : (σ y) = (M.op (σ y) (σ (k x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e109729
               have i₂ := b8e238 y x
               grind)
            | exact superpose b8e238 b8e109729
            | (have j1 := b8e238 y (k x y)
               grind)
            | exact resolve b8e109729 b8e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238 b8e109729
          have b8e110816 : (σ y) = (M.op (σ y) (σ (k x y))) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e110530
               have r₂ := b8e24
               grind)
            | exact resolve b8e110530 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110530
          have b8e115318 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ (k x y)) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ (k x y)) (σ y)
               have i₂ := b8e110816
               grind)
            | exact superpose b8e110816 b8e17
            | (have j0 := b8e17 (σ (k x y)) (σ y)
               grind)
            | (have r₁ := b8e17 (σ (k x y)) (σ y)
               have r₂ := b8e110816
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e110816
               grind)
            | exact resolve b8e17 b8e110816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110816
          have b8e115443 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ (k x y)) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e115318
          have b8e115480 : (σ y) = (k (σ (k x y)) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e115443
               have r₂ := b8e23
               grind)
            | exact resolve b8e115443 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115443
          have b8e115524 : (σ y) = (σ (k (k x y) y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e115480
               have i₂ := b8e19 (k x y) y
               grind)
            | exact superpose b8e19 b8e115480
            | exact resolve b8e115480 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115480
          have b8e118864 : (τ (σ y)) = (k (k x y) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k (k x y) y)
               have i₂ := b8e115524
               grind)
            | exact superpose b8e115524 b8e14
            | exact resolve b8e14 b8e115524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115524
          have b8e118951 : y = (k (k x y) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e118864
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e118864
            | exact resolve b8e118864 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118864
          have b8e121188 : y ≠ y ∨ y = (M.op y (k x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e29595 (k x y) y
               have i₂ := b8e118951
               grind)
            | exact superpose b8e118951 b8e29595
            | (have j0 := b8e29595 (k x y) y
               grind)
            | (have r₁ := b8e29595 (k x y) y
               have r₂ := b8e118951
               grind)
            | exact resolve b8e29595 b8e118951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29595 b8e118951
          have b8e121191 : y = (M.op y (k x y)) ∨ x = (M.op x y) := by grind
          clear b8e121188
          have b8e127439 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e121191
               have i₂ := b8e233 x y
               grind)
            | exact superpose b8e233 b8e121191
            | (have j1 := b8e233 (M.op y x) y
               grind)
            | exact resolve b8e121191 b8e233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e233 b8e121191
          have b8e127597 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e127439
               have r₂ := b8e22
               grind)
            | exact resolve b8e127439 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127439
          have b8e133829 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e118 y x X0
               have i₂ := b8e127597
               grind)
            | exact superpose b8e127597 b8e118
            | exact resolve b8e118 b8e127597
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127597
          have b8e139803 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e133829 (M.op x y)
               have i₂ := b8e133829 x
               grind)
            | exact superpose b8e133829 b8e133829
            | exact resolve b8e133829 b8e133829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133829
          have b8e140034 : x = (M.op x y) := by grind
          clear b8e139803
          have b8e140308 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e140034
               grind)
            | exact superpose b8e140034 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e140034
               grind)
            | exact resolve b8e17 b8e140034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e140327 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b8e118 x y X0
               have i₂ := b8e140034
               grind)
            | exact superpose b8e140034 b8e118
            | exact resolve b8e118 b8e140034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e140339 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op X1 x) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e132 X0 X1 x y
               have i₂ := b8e140034
               grind)
            | exact superpose b8e140034 b8e132
            | exact resolve b8e132 b8e140034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e140365 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b8e315 x X0 y
               have i₂ := b8e140034
               grind)
            | exact superpose b8e140034 b8e315
            | exact resolve b8e315 b8e140034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e315
          have b8e140444 : x = (k y x) ∨ x = (M.op x x) := by grind
          clear b8e140308
          have b8e140482 : y = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b8e140327 x
               have i₂ := b8e140339 x x
               grind)
            | exact superpose b8e140339 b8e140327
            | exact resolve b8e140327 b8e140339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140327 b8e140339
          have b8e141747 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op y (M.op (M.op X1 x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1201 X0 y y x X1
               have i₂ := b8e140482
               grind)
            | exact superpose b8e140482 b8e1201
            | exact resolve b8e1201 b8e140482
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1201 b8e140482
          have b8e160280 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e24498 x y
               have i₂ := b8e140444
               grind)
            | exact superpose b8e140444 b8e24498
            | (have j0 := b8e24498 x y
               grind)
            | exact resolve b8e24498 b8e140444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24498 b8e140444
          have b8e160285 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
          clear b8e160280
          have b8e270883 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e160285
               grind)
            | exact superpose b8e160285 b8e20
            | exact resolve b8e20 b8e160285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160285
          have b8e271149 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e270883
               have i₂ := b8e140034
               grind)
            | exact superpose b8e140034 b8e270883
            | exact resolve b8e270883 b8e140034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140034 b8e270883
          have b8e271150 : x = (M.op x x) := by grind
          clear b8e271149
          have b8e281833 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b8e140365 x
               have i₂ := b8e271150
               grind)
            | exact superpose b8e271150 b8e140365
            | exact resolve b8e140365 b8e271150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140365
          have b8e281838 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b8e141747 X0 x
               have i₂ := b8e271150
               grind)
            | exact superpose b8e271150 b8e141747
            | exact resolve b8e141747 b8e271150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141747
          have b8e282102 : y = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b8e281833
               have i₂ := b8e281838 x
               grind)
            | exact superpose b8e281838 b8e281833
            | exact resolve b8e281833 b8e281838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e281833 b8e281838
          have b8e282177 : y = (M.op y x) := by
            first
            | (have i₁ := b8e282102
               have i₂ := b8e271150
               grind)
            | exact superpose b8e271150 b8e282102
            | exact resolve b8e282102 b8e271150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e271150 b8e282102
          have b8e282230 : False := by grind
          exact b8e282230

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
      have b0e46 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e48 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e46
      have b0e49 : (M.op x x) = (k x y) := by grind
      clear b0e44
      have b0e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e48
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e48
        | exact resolve b0e48 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e51 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e50
           have i₂ := b0e49
           grind)
        | exact superpose b0e49 b0e50
        | exact resolve b0e50 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e50
      have b0e52 : False := by grind
      exact b0e52
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : (M.op x x) = (k x y) := by grind
        clear b2e51
        have b2e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e53 (σ X0)
             grind)
          | exact superpose b2e53 b2e18
          | exact resolve b2e18 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e56 X0
             have i₂ := b2e53 X0
             grind)
          | exact superpose b2e53 b2e56
          | exact resolve b2e56 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e56
        have b2e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0 X1
             have i₂ := b2e63 X0
             grind)
          | exact superpose b2e63 b2e71
          | (have j0 := b2e71 X0 X1
             grind)
          | exact resolve b2e71 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e763 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e87 x y
             grind)
          | exact superpose b2e87 b2e21
          | (have j1 := b2e87 x y
             grind)
          | exact resolve b2e21 b2e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e828 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e763
             have r₂ := b2e24
             grind)
          | exact resolve b2e763 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e763
        have b2e841 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e828
             have r₂ := b2e22
             grind)
          | exact resolve b2e828 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e828
        have b2e847 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e841
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e841
          | exact resolve b2e841 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e841
        have b2e849 : False := by grind
        exact b2e849
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e52
        have b6e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e92 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e55
             grind)
          | exact superpose b6e55 b6e24
          | exact resolve b6e24 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e55
        have b6e127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b6e92
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e92
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e92
             have r₂ := b6e17 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e92
             have r₂ := b6e17 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e92 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e128 : (M.op x y) = (M.op x x) ∨ x = y := by grind
        clear b6e127
        have b6e129 : x = y := by
          first
          | (have r₁ := b6e128
             have r₂ := b6e20
             grind)
          | exact resolve b6e128 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e130 : False := by grind
        exact b6e130
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e43 (σ X0)
               grind)
            | exact superpose b8e43 b8e19
            | exact resolve b8e19 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e45 X0
               have i₂ := b8e43 X0
               grind)
            | exact superpose b8e43 b8e45
            | exact resolve b8e45 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43 b8e45
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e64 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e56 X0 X1
               have i₂ := b8e50 X0
               grind)
            | exact superpose b8e50 b8e56
            | (have j0 := b8e56 X0 X1
               grind)
            | exact resolve b8e56 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e179 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e182 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e179 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e179 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e179 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e179 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e179 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179
          have b8e630 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e71 x y
               grind)
            | exact superpose b8e71 b8e20
            | (have j1 := b8e71 x y
               grind)
            | exact resolve b8e20 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e694 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e630
               have r₂ := b8e24
               grind)
            | exact resolve b8e630 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e630
          have b8e2702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b8e694
               have i₂ := b8e182 x y
               grind)
            | exact superpose b8e182 b8e694
            | (have j1 := b8e182 (M.op (σ x) (σ y)) (σ (M.op x x))
               grind)
            | (have r₁ := b8e694
               have r₂ := b8e182 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e694
               have r₂ := b8e182 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e694 b8e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e182 b8e694
          have b8e2707 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b8e2702
          have b8e2712 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e2707
               have r₂ := b8e22
               grind)
            | exact resolve b8e2707 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2707
          have b8e2717 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e2712
               grind)
            | exact superpose b8e2712 b8e23
            | exact resolve b8e23 b8e2712
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2712
          have b8e2758 : False := by grind
          exact b8e2758

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
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
      have b0e42 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e45 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e43
      have b0e46 : (M.op x x) = (k x y) := by grind
      clear b0e42
      have b0e47 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e45
        | exact resolve b0e45 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e48 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e47
        | exact resolve b0e47 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e47
      have b0e69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X0 X0) (M.op X1 X0)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e69 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e285 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e73 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73
      have b0e288 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e285 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e285 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e285 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e285 X0 X1
           have r₂ := b0e16 (M.op X0 X0) (M.op X1 X0)
           grind)
        | exact resolve b0e285 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e285
      have b0e487 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e288 X1 (τ X0)
           grind)
        | exact superpose b0e288 b0e23
        | (have j1 := b0e288 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e288
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e288 (σ X1) (σ X0)
           grind)
        | exact superpose b0e288 b0e17
        | (have j1 := b0e288 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e288
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e288
      have b0e5856 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e487 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e487
        | exact resolve b0e487 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e487
      have b0e5977 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e5856 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e5856
        | (have j0 := b0e5856 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e5856 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5856
      have b0e14352 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e488 x y
           grind)
        | exact superpose b0e488 b0e18
        | (have j1 := b0e488 x y
           grind)
        | exact resolve b0e18 b0e488
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e488
      have b0e14543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e14352
           have i₂ := b0e5977 x y
           grind)
        | exact superpose b0e5977 b0e14352
        | (have j1 := b0e5977 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14352
           have r₂ := b0e5977 x y
           grind)
        | (have r₁ := b0e14352
           have r₂ := b0e5977 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e14352
           have r₂ := b0e5977 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e14352 b0e5977
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5977 b0e14352
      have b0e14544 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e14543
      have b0e14926 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e14544
           grind)
        | exact superpose b0e14544 b0e12
        | exact resolve b0e12 b0e14544
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14544
      have b0e14980 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e14926
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e14926
        | exact resolve b0e14926 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14926
      have b0e14981 : x = y := by grind
      clear b0e14980
      have b0e15845 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e14981
           grind)
        | exact superpose b0e14981 b0e18
        | exact resolve b0e18 b0e14981
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14981
      have b0e15879 : False := by grind
      exact b0e15879
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (M.op x x) = (k x y) := by grind
        clear b2e50
        have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e51 (σ X0)
             grind)
          | exact superpose b2e51 b2e18
          | exact resolve b2e18 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e51 X0
             grind)
          | exact superpose b2e51 b2e54
          | exact resolve b2e54 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e54
        have b2e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e69 X0 X1
             have i₂ := b2e61 X1
             grind)
          | exact superpose b2e61 b2e69
          | (have j0 := b2e69 X0 X1
             grind)
          | exact resolve b2e69 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69
        have b2e483 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e85 y x
             grind)
          | exact superpose b2e85 b2e21
          | (have j1 := b2e85 y x
             grind)
          | exact resolve b2e21 b2e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e532 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e483
             have r₂ := b2e22
             grind)
          | exact resolve b2e483 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e483
        have b2e546 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e532
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e532
          | exact resolve b2e532 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e532
        have b2e552 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e546
             have r₂ := b2e61 x
             grind)
          | exact resolve b2e546 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e546
        have b2e556 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e552
             grind)
          | exact superpose b2e552 b2e21
          | exact resolve b2e21 b2e552
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e552
        have b2e572 : False := by grind
        exact b2e572
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e50
        have b6e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e52
          | exact resolve b6e52 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e89 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e15
          | exact resolve b6e15 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e94 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e89
        have b6e95 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e94
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e94
          | exact resolve b6e94 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e94
        have b6e96 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e95
             have i₂ := b6e51 x
             grind)
          | exact superpose b6e51 b6e95
          | exact resolve b6e95 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e95
        have b6e163 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e96
             grind)
          | exact superpose b6e96 b6e13
          | exact resolve b6e13 b6e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e164 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e163
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e163
          | exact resolve b6e163 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e163
        have b6e209 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e164
             grind)
          | exact superpose b6e164 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e164
        have b6e210 : (M.op x x) = (M.op y x) ∨ x = y := by grind
        clear b6e209
        have b6e212 : x = y := by
          first
          | (have r₁ := b6e210
             have r₂ := b6e20
             grind)
          | exact resolve b6e210 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e210
        have b6e214 : False := by grind
        exact b6e214
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e27 X1 X0
               grind)
            | exact superpose b8e27 b8e14
            | exact resolve b8e14 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e42 (σ X0)
               grind)
            | exact superpose b8e42 b8e19
            | exact resolve b8e19 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e44
            | exact resolve b8e44 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e44
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X1 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e55 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e55
            | (have j0 := b8e55 X0 X1
               grind)
            | exact resolve b8e55 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e55
          have b8e174 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e67 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e177 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e174 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e174 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e174 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e174 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X1 X0)
               grind)
            | exact resolve b8e174 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e342 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e39 X1 X0
               have i₂ := b8e177 (σ X1) X0
               grind)
            | exact superpose b8e177 b8e39
            | (have j1 := b8e177 (k X1 (τ X0)) (τ (M.op X0 (σ X1)))
               grind)
            | exact resolve b8e39 b8e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e438 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
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
          have b8e489 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e438
               have r₂ := b8e24
               grind)
            | exact resolve b8e438 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e438
          have b8e1859 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have i₁ := b8e489
               have i₂ := b8e177 y x
               grind)
            | exact superpose b8e177 b8e489
            | (have j1 := b8e177 (M.op (σ x) (σ y)) (σ (M.op y y))
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e177 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e177 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e489 b8e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e489
          have b8e1863 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by grind
          clear b8e1859
          have b8e1867 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e1863
               have r₂ := b8e22
               grind)
            | exact resolve b8e1863 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1863
          have b8e1871 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1867
               grind)
            | exact superpose b8e1867 b8e20
            | exact resolve b8e20 b8e1867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e5183 : (k y (τ (σ x))) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e342 (σ x) y
               have i₂ := b8e1867
               grind)
            | exact superpose b8e1867 b8e342
            | (have j0 := b8e342 (σ y) x
               grind)
            | exact resolve b8e342 b8e1867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e342 b8e1867
          have b8e5210 : (k y (τ (σ x))) = (τ (σ (M.op y y))) := by
            first
            | (have r₁ := b8e5183
               have r₂ := b8e24
               grind)
            | exact resolve b8e5183 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5183
          have b8e5218 : (M.op y y) = (k y (τ (σ x))) := by
            first
            | (have i₁ := b8e5210
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e5210
            | exact resolve b8e5210 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5210
          have b8e5221 : (k y x) = (M.op y y) := by
            first
            | (have i₁ := b8e5218
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e5218
            | exact resolve b8e5218 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5218
          have b8e5462 : (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e177 y x
               have i₂ := b8e5221
               grind)
            | exact superpose b8e5221 b8e177
            | (have j0 := b8e177 (M.op x y) (M.op y y)
               grind)
            | exact resolve b8e177 b8e5221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177 b8e5221
          have b8e5465 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e5462
               have r₂ := b8e22
               grind)
            | exact resolve b8e5462 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5462
          have b8e5678 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e1871
               have i₂ := b8e5465
               grind)
            | exact superpose b8e5465 b8e1871
            | exact resolve b8e1871 b8e5465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1871 b8e5465
          have b8e5743 : False := by grind
          exact b8e5743

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e42 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
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
      have b0e43 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
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
      have b0e257 : (M.op x y) = (k y x) := by
        first
        | (have j0 := b0e42 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e424 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have j0 := b0e43 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e426 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e424
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e424
        | exact resolve b0e424 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e424
      have b0e432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e426
           have i₂ := b0e257
           grind)
        | exact superpose b0e257 b0e426
        | exact resolve b0e426 b0e257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e257 b0e426
      have b0e435 : False := by grind
      exact b0e435
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e52 (σ X0)
             grind)
          | exact superpose b2e52 b2e18
          | exact resolve b2e18 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e52 X0
             grind)
          | exact superpose b2e52 b2e54
          | exact resolve b2e54 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e54
        have b2e141 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e61 y
             grind)
          | exact superpose b2e61 b2e21
          | exact resolve b2e21 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e150 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e141
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e141
          | exact resolve b2e141 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e141
        have b2e153 : False := by grind
        exact b2e153
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e52 (σ X0)
             grind)
          | exact superpose b6e52 b6e18
          | exact resolve b6e18 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e54 X0
             have i₂ := b6e52 X0
             grind)
          | exact superpose b6e52 b6e54
          | exact resolve b6e54 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52 b6e54
        have b6e135 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e61 y
             grind)
          | exact superpose b6e61 b6e22
          | exact resolve b6e22 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e144 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e135
             have i₂ := b6e61 x
             grind)
          | exact superpose b6e61 b6e135
          | exact resolve b6e135 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e135
        have b6e161 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e144
             grind)
          | exact superpose b6e144 b6e13
          | exact resolve b6e13 b6e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e162 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e161
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e161
          | exact resolve b6e161 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161
        have b6e168 : False := by grind
        exact b6e168
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e42 (σ X0)
               grind)
            | exact superpose b8e42 b8e19
            | exact resolve b8e19 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e44
            | exact resolve b8e44 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e44
          have b8e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e67 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ y = X0 := by
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
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e77
            | (have j0 := b8e77 X0 X1
               grind)
            | exact resolve b8e77 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e163 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e67 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e164 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e163
               have r₂ := b8e22
               grind)
            | exact resolve b8e163 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e163
          have b8e228 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e49 y
               grind)
            | exact superpose b8e49 b8e23
            | exact resolve b8e23 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e243 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e228
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e228
            | exact resolve b8e228 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e228
          have b8e963 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e83 x y
               grind)
            | exact superpose b8e83 b8e20
            | (have j1 := b8e83 x y
               grind)
            | exact resolve b8e20 b8e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e1007 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e963
               have r₂ := b8e243
               grind)
            | exact resolve b8e963 b8e243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e243 b8e963
          have b8e1016 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e1007
               have r₂ := b8e24
               grind)
            | exact resolve b8e1007 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1007
          have b8e1019 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e1016
               have i₂ := b8e164
               grind)
            | exact superpose b8e164 b8e1016
            | exact resolve b8e1016 b8e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164 b8e1016
          have b8e1020 : False := by grind
          exact b8e1020

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_pxy_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 y))) = X0 := by
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
      have b0e30 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) = X0 := by
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
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
           have i₂ := b0e11 X0 X2 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b0e29 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e29
        | exact resolve b0e29 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e38 : (k x y) = (M.op y x) := by grind
      have b0e39 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
      have b0e40 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e39
        | exact resolve b0e39 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e41 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e40
        | exact resolve b0e40 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e40
      have b0e97 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b0e30 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30
        | exact resolve b0e30 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e209 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e31 X0 X0 x x
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e31
        | exact resolve b0e31 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e225 : y = (M.op y x) := by
        first
        | (have i₁ := b0e209 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e209
        | exact resolve b0e209 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e229 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op X0 X0)
           have i₂ := b0e209 X0
           grind)
        | exact superpose b0e209 b0e11
        | exact resolve b0e11 b0e209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e209
      have b0e291 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e225
           grind)
        | exact superpose b0e225 b0e11
        | exact resolve b0e11 b0e225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e599 : x = (M.op x y) := by
        first
        | (have i₁ := b0e291 x
           have i₂ := b0e35
           grind)
        | exact superpose b0e35 b0e291
        | exact resolve b0e291 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e291
      have b0e1308 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b0e229 (σ x) (σ y)
           have i₂ := b0e97
           grind)
        | exact superpose b0e97 b0e229
        | exact resolve b0e229 b0e97
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97 b0e229
      have b0e1324 : (σ x) = (M.op (σ x) (σ (M.op y x))) := by
        first
        | (have i₁ := b0e1308
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e1308
        | exact resolve b0e1308 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e1308
      have b0e1327 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e1324
           have i₂ := b0e225
           grind)
        | exact superpose b0e225 b0e1324
        | exact resolve b0e1324 b0e225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e225 b0e1324
      have b0e1619 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1327
           grind)
        | exact superpose b0e1327 b0e18
        | exact resolve b0e18 b0e1327
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1327
      have b0e1635 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e1619
           have i₂ := b0e599
           grind)
        | exact superpose b0e599 b0e1619
        | exact resolve b0e1619 b0e599
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e599 b0e1619
      have b0e1636 : False := by grind
      exact b0e1636
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
             have i₂ := b1e12 X0 X2 X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : (k x y) = (M.op y x) := by grind
        have b1e64 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e76 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e64
             have r₂ := b1e21
             grind)
          | exact resolve b1e64 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e77 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e76
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e76
          | exact resolve b1e76 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e78 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e77
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e77
          | exact resolve b1e77 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e77
        have b1e224 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e29 X0 X0 x x
             have i₂ := b1e12 X0 x x
             grind)
          | exact superpose b1e12 b1e29
          | exact resolve b1e29 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e241 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e224 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e224
          | exact resolve b1e224 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e242 : y = (M.op y x) := by
          first
          | (have i₁ := b1e224 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e224
          | exact resolve b1e224 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e224
        have b1e327 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e78
             have i₂ := b1e241
             grind)
          | exact superpose b1e241 b1e78
          | exact resolve b1e78 b1e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e337 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e327
             have i₂ := b1e242
             grind)
          | exact superpose b1e242 b1e327
          | exact resolve b1e327 b1e242
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e242 b1e327
        have b1e343 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e337
             grind)
          | exact superpose b1e337 b1e19
          | exact resolve b1e19 b1e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e350 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e241
             have i₂ := b1e337
             grind)
          | exact superpose b1e337 b1e241
          | exact resolve b1e241 b1e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e241
        have b1e355 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e337
             grind)
          | exact superpose b1e337 b1e13
          | exact resolve b1e13 b1e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e356 : x = y := by
          first
          | (have i₁ := b1e355
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e355
          | exact resolve b1e355 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e355
        have b1e363 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e343
             have i₂ := b1e350
             grind)
          | exact superpose b1e350 b1e343
          | exact resolve b1e343 b1e350
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e343 b1e350
        have b1e365 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e363
             have i₂ := b1e356
             grind)
          | exact superpose b1e356 b1e363
          | exact resolve b1e363 b1e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e356 b1e363
        have b1e366 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e365
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e365
          | exact resolve b1e365 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e365
        have b1e367 : False := by grind
        exact b1e367
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 y))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : y = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b2e27 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e27
          | exact resolve b2e27 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e50 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ y) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ y) (σ y))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ y) X0
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
        have b2e53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e40 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e57 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e68 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        clear b2e53
        have b2e160 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e28 X0 X0 x x
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e171 : y = (M.op y x) := by
          first
          | (have i₁ := b2e160 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e160
          | exact resolve b2e160 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e180 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X0 X0)
             have i₂ := b2e160 X0
             grind)
          | exact superpose b2e160 b2e12
          | exact resolve b2e12 b2e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e160
        have b2e229 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e171
             grind)
          | exact superpose b2e171 b2e12
          | exact resolve b2e12 b2e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e329 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have j0 := b2e50 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e330 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e329
             have r₂ := b2e22
             grind)
          | exact resolve b2e329 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e329
        have b2e331 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e330
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e330
          | exact resolve b2e330 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e330
        have b2e333 : x = (M.op x y) := by
          first
          | (have i₁ := b2e229 x
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e229
          | exact resolve b2e229 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e229
        have b2e369 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        clear b2e68
        have b2e412 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e369 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e369
        have b2e728 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e331
             grind)
          | exact superpose b2e331 b2e19
          | exact resolve b2e19 b2e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e739 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e728
             have i₂ := b2e333
             grind)
          | exact superpose b2e333 b2e728
          | exact resolve b2e728 b2e333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e728
        have b2e2177 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e180 X0 (M.op X1 X0)
             have i₂ := b2e12 X0 X1 X0
             grind)
          | exact superpose b2e12 b2e180
          | exact resolve b2e180 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180
        have b2e2483 : (σ (k y x)) = (M.op (σ (k y x)) (σ y)) := by
          first
          | (have i₁ := b2e2177 (σ y) (σ x)
             have i₂ := b2e331
             grind)
          | exact superpose b2e331 b2e2177
          | exact resolve b2e2177 b2e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e331 b2e2177
        have b2e3030 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e98 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e3031 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e3030 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3030
        have b2e3045 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e3031 (σ X0)
             grind)
          | exact superpose b2e3031 b2e18
          | exact resolve b2e18 b2e3031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3052 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3045 X0
             have i₂ := b2e3031 X0
             grind)
          | exact superpose b2e3031 b2e3045
          | exact resolve b2e3045 b2e3031
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3031 b2e3045
        have b2e3080 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b2e739
             have i₂ := b2e412 y x
             grind)
          | exact superpose b2e412 b2e739
          | (have j1 := b2e412 y x
             grind)
          | exact resolve b2e739 b2e412
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e412
        have b2e3115 : (σ x) ≠ (σ x) ∨ (M.op y x) = (k y x) := by
          first
          | (have i₁ := b2e3080
             have i₂ := b2e333
             grind)
          | exact superpose b2e333 b2e3080
          | exact resolve b2e3080 b2e333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e333 b2e3080
        have b2e3116 : (M.op y x) = (k y x) := by grind
        clear b2e3115
        have b2e3122 : y = (k y x) := by
          first
          | (have i₁ := b2e3116
             have i₂ := b2e171
             grind)
          | exact superpose b2e171 b2e3116
          | exact resolve b2e3116 b2e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171 b2e3116
        have b2e3135 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e2483
             have i₂ := b2e3122
             grind)
          | exact superpose b2e3122 b2e2483
          | exact resolve b2e2483 b2e3122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2483
        have b2e3136 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e739
             have i₂ := b2e3122
             grind)
          | exact superpose b2e3122 b2e739
          | exact resolve b2e739 b2e3122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e739 b2e3122
        have b2e3148 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e3135
             have i₂ := b2e3052 y
             grind)
          | exact superpose b2e3052 b2e3135
          | exact resolve b2e3135 b2e3052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3052 b2e3135
        have b2e3150 : (σ x) = (σ y) := by
          first
          | (have i₁ := b2e3148
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3148
          | exact resolve b2e3148 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3148
        have b2e3152 : False := by grind
        exact b2e3152
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
             have i₂ := b3e12 X0 X2 X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
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
        have b3e63 : x = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
        have b3e74 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e63
             have r₂ := b3e20
             grind)
          | exact resolve b3e63 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e205 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e29 X0 X0 x x
             have i₂ := b3e12 X0 x x
             grind)
          | exact superpose b3e12 b3e29
          | exact resolve b3e29 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e222 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e205 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e205
          | exact resolve b3e205 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e223 : x = (M.op x y) := by
          first
          | (have i₁ := b3e205 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e205
          | exact resolve b3e205 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e205
        have b3e304 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e38
             have i₂ := b3e222
             grind)
          | exact superpose b3e222 b3e38
          | exact resolve b3e38 b3e222
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e222
        have b3e311 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b3e304
             have i₂ := b3e74
             grind)
          | exact superpose b3e74 b3e304
          | exact resolve b3e304 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74 b3e304
        have b3e313 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e311
             have i₂ := b3e223
             grind)
          | exact superpose b3e223 b3e311
          | exact resolve b3e311 b3e223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e311
        have b3e347 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e313
             grind)
          | exact superpose b3e313 b3e19
          | exact resolve b3e19 b3e313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e358 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e347
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e347
          | exact resolve b3e347 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e347
        have b3e360 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e358
             have i₂ := b3e313
             grind)
          | exact superpose b3e313 b3e358
          | exact resolve b3e358 b3e313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e358
        have b3e362 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e360
             have i₂ := b3e223
             grind)
          | exact superpose b3e223 b3e360
          | exact resolve b3e360 b3e223
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e223 b3e360
        have b3e364 : False := by grind
        exact b3e364
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e42 : (M.op x y) = (k y x) := by grind
          have b4e43 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e44 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e43
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e43
            | exact resolve b4e43 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e45 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e44
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e44
            | exact resolve b4e44 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e44
          have b4e46 : False := by grind
          exact b4e46
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b5e40 : (M.op x y) = (k y x) := by grind
          have b5e56 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ y) X0
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
          have b5e315 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e56 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e316 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e315
               have r₂ := b5e24
               grind)
            | exact resolve b5e315 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e315
          have b5e317 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e316
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e316
            | exact resolve b5e316 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e316
          have b5e318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e317
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e317
            | exact resolve b5e317 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e317
          have b5e319 : False := by grind
          exact b5e319
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e27 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
             have i₂ := b6e12 X0 X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        have b6e36 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e94 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b6e27 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e27
          | exact resolve b6e27 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e184 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e28 X0 X0 x x
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e28
          | exact resolve b6e28 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e195 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e184 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e184
          | exact resolve b6e184 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e203 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (M.op X0 X0)
             have i₂ := b6e184 X0
             grind)
          | exact superpose b6e184 b6e12
          | exact resolve b6e12 b6e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e184
        have b6e251 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e36
             have i₂ := b6e195
             grind)
          | exact superpose b6e195 b6e36
          | exact resolve b6e36 b6e195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e195
        have b6e270 : (σ y) = (σ (M.op y x)) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e251
             have i₂ := b6e66 x y
             grind)
          | exact superpose b6e66 b6e251
          | (have j1 := b6e66 x y
             grind)
          | exact resolve b6e251 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e283 : (σ y) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e270
             have r₂ := b6e21
             grind)
          | exact resolve b6e270 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e270
        have b6e809 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b6e203 (σ x) (σ y)
             have i₂ := b6e94
             grind)
          | exact superpose b6e94 b6e203
          | exact resolve b6e203 b6e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e94 b6e203
        have b6e820 : (σ x) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b6e809
             have i₂ := b6e36
             grind)
          | exact superpose b6e36 b6e809
          | exact resolve b6e809 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36 b6e809
        have b6e823 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e820
             have i₂ := b6e251
             grind)
          | exact superpose b6e251 b6e820
          | exact resolve b6e820 b6e251
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e251 b6e820
        have b6e883 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e823
             grind)
          | exact superpose b6e823 b6e19
          | exact resolve b6e19 b6e823
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e823
        have b6e1490 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e64 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64
          | exact resolve b6e64 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e1741 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e1490
        have b6e2430 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e1741
             grind)
          | exact superpose b6e1741 b6e13
          | exact resolve b6e13 b6e1741
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1741
        have b6e2444 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2430
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2430
          | exact resolve b6e2430 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2430
        have b6e2640 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e126 y y
             have i₂ := b6e2444
             grind)
          | exact superpose b6e2444 b6e126
          | exact resolve b6e126 b6e2444
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126 b6e2444
        have b6e2663 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e2640
        have b6e2671 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2663
             have r₂ := b6e20
             grind)
          | exact resolve b6e2663 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2663
        have b6e2688 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e2671
             grind)
          | exact superpose b6e2671 b6e13
          | exact resolve b6e13 b6e2671
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2671
        have b6e2705 : x = y := by
          first
          | (have i₁ := b6e2688
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2688
          | exact resolve b6e2688 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2688
        have b6e2793 : (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e283
             have i₂ := b6e2705
             grind)
          | exact superpose b6e2705 b6e283
          | exact resolve b6e283 b6e2705
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e283
        have b6e2799 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e883
             have i₂ := b6e2705
             grind)
          | exact superpose b6e2705 b6e883
          | exact resolve b6e883 b6e2705
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e883 b6e2705
        have b6e2801 : False := by grind
        exact b6e2801
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e45 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b7e47 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e45
            | exact resolve b7e45 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e48 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e20
            | exact resolve b7e20 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e74 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e48
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e48 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e75 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b7e74
          have b7e76 : x = (M.op y y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e77 : False := by grind
          exact b7e77
        · have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e132 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e74 (σ y) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e74 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e74 b8e23
            | (have j1 := b8e74 (σ y) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e74 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e134 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e132 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e135 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e134
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e134
            | exact resolve b8e134 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e232 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e135
               grind)
            | exact superpose b8e135 b8e20
            | exact resolve b8e20 b8e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e232
               have i₂ := b8e74 y x
               grind)
            | exact superpose b8e74 b8e232
            | (have j1 := b8e74 y x
               grind)
            | exact resolve b8e232 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74 b8e232
          have b8e244 : x = (M.op y y) := by grind
          clear b8e241
          have b8e246 : False := by grind
          exact b8e246
