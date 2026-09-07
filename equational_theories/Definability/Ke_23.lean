import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation834`: `x = x ◇ ((y ◇ x) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_x_pxx_pyx_Equation834 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law834 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law834.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, x = (M.op x (M.op y (M.op x X0))) := by
        intro X0
        first
        | (have i₁ := b0e11 x y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op (M.op x X0) (M.op X0 x))
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : x = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b0e33 (M.op (M.op x x) (M.op x x))
           have i₂ := b0e11 x x x
           grind)
        | exact superpose b0e11 b0e33
        | exact resolve b0e33 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e47 : x = (M.op x y) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e42
        | exact resolve b0e42 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e68 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b0e38 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e38
        | exact resolve b0e38 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e81 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e68
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e68
        | exact resolve b0e68 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e84 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e81
           grind)
        | exact superpose b0e81 b0e18
        | exact resolve b0e18 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e92 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e84
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e84
        | exact resolve b0e84 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e84
      have b0e93 : False := by grind
      exact b0e93
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e28 : y = (M.op y y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e20
          | exact resolve b1e20 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 y y
             have r₂ := b1e28
             grind)
          | exact resolve b1e15 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : y = (k y y) := by grind
        clear b1e30
        have b1e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e154 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e65 y
             grind)
          | exact superpose b1e65 b1e25
          | (have j1 := b1e65 y
             grind)
          | exact resolve b1e25 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e65
        have b1e164 : (σ (M.op x y)) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e154
             have r₂ := b1e24
             grind)
          | exact resolve b1e154 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e154
        have b1e168 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e164
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e164
          | exact resolve b1e164 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e164
        have b1e171 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e168
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e168
          | exact resolve b1e168 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e168
        have b1e173 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e171
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e171
          | exact resolve b1e171 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e171
        have b1e174 : False := by grind
        exact b1e174
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
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
        have b2e28 : ∀ X0 : G, x = (M.op x (M.op y (M.op x X0))) := by
          intro X0
          first
          | (have i₁ := b2e12 x y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : x = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b2e28 (M.op (M.op x x) (M.op x x))
             have i₂ := b2e12 x x x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e40 : x = (M.op x y) := by
          first
          | (have i₁ := b2e35
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e35
          | exact resolve b2e35 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e47 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e40
             grind)
          | exact resolve b2e15 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : y = (k y x) := by grind
        clear b2e47
        have b2e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e171 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (M.op X2 (σ X1)) (σ (k X0 X1)))) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X1) X2 (σ X0)
             have i₂ := b2e53 X1 X0
             grind)
          | exact superpose b2e53 b2e12
          | (have j1 := b2e53 X0 X1
             grind)
          | exact resolve b2e12 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e172 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op (σ X0) X2))) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X0) (σ X1) X2
             have i₂ := b2e53 X1 X0
             grind)
          | exact superpose b2e53 b2e12
          | (have j1 := b2e53 X0 X1
             grind)
          | exact resolve b2e12 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e174 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1844 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e171 y x X0
             have i₂ := b2e48
             grind)
          | exact superpose b2e48 b2e171
          | (have j0 := b2e171 x y x
             grind)
          | exact resolve b2e171 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171
        have b2e1873 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e1844 X0
             grind)
          | (have r₁ := b2e1844 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e1844 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1844
        have b2e1929 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) X0))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e172 x y X0
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e172
          | (have j0 := b2e172 x y x
             grind)
          | exact resolve b2e172 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e172
        have b2e1980 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) X0))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have j0 := b2e1929 X0
             grind)
          | (have r₁ := b2e1929 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e1929 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1929
        have b2e1986 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) X0))) := by
          intro X0
          first
          | (have j0 := b2e1980 X0
             grind)
          | (have r₁ := b2e1980 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e1980 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1980
        have b2e2149 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e1986 (M.op (σ x) x)
             have i₂ := b2e1986 x
             grind)
          | exact superpose b2e1986 b2e1986
          | exact resolve b2e1986 b2e1986
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1986
        have b2e76380 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1873 (σ x)
             have i₂ := b2e2149
             grind)
          | exact superpose b2e2149 b2e1873
          | exact resolve b2e1873 b2e2149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1873 b2e2149
        have b2e76575 : (σ x) = (M.op (σ x) (σ (k y x))) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e76380
             have i₂ := b2e53 x y
             grind)
          | exact superpose b2e53 b2e76380
          | (have j1 := b2e53 x (k y x)
             grind)
          | exact resolve b2e76380 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e76380
        have b2e76664 : (σ x) = (M.op (σ x) (σ (k y x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j1 := b2e174 x y
             grind)
          | (have r₁ := b2e76575
             have r₂ := b2e174 x y
             grind)
          | exact resolve b2e76575 b2e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174 b2e76575
        have b2e76666 : (σ x) = (M.op (σ x) (σ (k y x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e76664
             have r₂ := b2e22
             grind)
          | exact resolve b2e76664 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76664
        have b2e76667 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e76666
             have i₂ := b2e48
             grind)
          | exact superpose b2e48 b2e76666
          | exact resolve b2e76666 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e76666
        have b2e76668 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e76667
        have b2e76793 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e76668
             grind)
          | exact superpose b2e76668 b2e19
          | exact resolve b2e19 b2e76668
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76668
        have b2e76970 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e76793
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e76793
          | exact resolve b2e76793 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e76793
        have b2e76971 : False := by grind
        exact b2e76971
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
        have b3e29 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e28
        have b3e30 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e29
          | exact resolve b3e29 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e32 : y = (k y y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e57 : y = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e32
        have b3e60 : y = (M.op y y) := by grind
        clear b3e57
        have b3e63 : False := by grind
        exact b3e63
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e88 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e45
          have b4e97 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e88
          have b4e100 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e97
          have b4e101 : y = (M.op y y) := by grind
          clear b4e100
          have b4e102 : False := by grind
          exact b4e102
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ y := by grind
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
        have b6e42 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (M.op (M.op x X0) (M.op X0 x))
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b6e42 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e42
          | exact resolve b6e42 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e54 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e45
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e45
          | exact resolve b6e45 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e59 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e19
          | exact resolve b6e19 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e15 (σ y) (σ x)
             have r₂ := b6e54
             grind)
          | exact resolve b6e15 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e64 : (σ y) = (k (σ y) (σ x)) := by grind
        clear b6e63
        have b6e65 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e64
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e64
          | exact resolve b6e64 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e71 : x = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
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
        have b6e74 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e71
             have r₂ := b6e21
             grind)
          | exact resolve b6e71 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e77 : x = (M.op y x) := by
          first
          | (have r₁ := b6e74
             have r₂ := b6e20
             grind)
          | exact resolve b6e74 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e81 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) x)) := by
          intro X0
          first
          | (have i₁ := b6e12 y X0 x
             have i₂ := b6e77
             grind)
          | exact superpose b6e77 b6e12
          | exact resolve b6e12 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e133 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e13
          | exact resolve b6e13 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e134 : y = (k y x) := by
          first
          | (have i₁ := b6e133
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e133
          | exact resolve b6e133 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e133
        have b6e158 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e134
             grind)
          | exact superpose b6e134 b6e17
          | (have j0 := b6e17 y (M.op x y)
             grind)
          | exact resolve b6e17 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e159 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e158
             have r₂ := b6e21
             grind)
          | exact resolve b6e158 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e158
        have b6e759 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e59
             have i₂ := b6e159
             grind)
          | exact superpose b6e159 b6e59
          | exact resolve b6e59 b6e159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e159
        have b6e779 : y = (M.op x y) := by grind
        clear b6e759
        have b6e818 : y = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b6e81 x
             have i₂ := b6e779
             grind)
          | exact superpose b6e779 b6e81
          | exact resolve b6e81 b6e779
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e779
        have b6e832 : y = (M.op y x) := by
          first
          | (have i₁ := b6e818
             have i₂ := b6e77
             grind)
          | exact superpose b6e77 b6e818
          | exact resolve b6e818 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77 b6e818
        have b6e836 : False := by grind
        exact b6e836
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e29 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 (M.op (M.op x X0) (M.op X0 x))
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op X1 X0) (M.op X0 X2)) (M.op X0 (M.op (M.op X1 X0) (M.op X0 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e29 (M.op (M.op X1 X0) (M.op X0 X2)) X0
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e29
            | exact resolve b8e29 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op (M.op X1 X0) X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (M.op (M.op X1 X0) X0) X0
               have i₂ := b8e29 X0 X1
               grind)
            | exact superpose b8e29 b8e16
            | (have j0 := b8e16 (M.op (M.op X1 X0) X0) X0
               grind)
            | (have r₁ := b8e16 (M.op (M.op X1 X0) X0) X0
               have r₂ := b8e29 X0 X1
               grind)
            | exact resolve b8e16 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op (M.op X1 X0) X0) X0) := by
            intro X0 X1
            first
            | (have j0 := b8e36 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e39 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X1 X2
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e26 X0 X1
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e115 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e49 x y
               grind)
            | exact superpose b8e49 b8e20
            | (have j1 := b8e49 x y
               grind)
            | exact resolve b8e20 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e123 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e115
               have r₂ := b8e24
               grind)
            | exact resolve b8e115 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e171 : ∀ X0 X1 : G, (τ (M.op (M.op X0 (σ X1)) (σ X1))) = (k (τ (M.op (M.op X0 (σ X1)) (σ X1))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e46 (M.op (M.op X0 (σ X1)) (σ X1)) X1
               have i₂ := b8e37 (σ X1) X0
               grind)
            | exact superpose b8e37 b8e46
            | exact resolve b8e46 b8e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37 b8e46
          have b8e540 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e123
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e123
            | (have j1 := b8e18 (σ x) (M.op (σ x) (σ y))
               grind)
            | (have r₁ := b8e123
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e123
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e123 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e541 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e540
          have b8e542 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e541
               have r₂ := b8e22
               grind)
            | exact resolve b8e541 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e541
          have b8e550 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e542
               grind)
            | exact superpose b8e542 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e542
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e542
               grind)
            | exact resolve b8e16 b8e542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e563 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e550
          have b8e564 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e563
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e563
            | exact resolve b8e563 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e563
          have b8e620 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e564
               grind)
            | exact superpose b8e564 b8e14
            | exact resolve b8e14 b8e564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e564
          have b8e651 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e620
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e620
            | exact resolve b8e620 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e620
          have b8e653 : y = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e651
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e651 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e651
          have b8e686 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e18 y x
               have i₂ := b8e653
               grind)
            | exact superpose b8e653 b8e18
            | (have j0 := b8e18 y (M.op x y)
               grind)
            | exact resolve b8e18 b8e653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e653
          have b8e687 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e686
               have r₂ := b8e22
               grind)
            | exact resolve b8e686 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e686
          have b8e746 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e29 y x
               have i₂ := b8e687
               grind)
            | exact superpose b8e687 b8e29
            | exact resolve b8e29 b8e687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29
          have b8e872 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e746
               have i₂ := b8e687
               grind)
            | exact superpose b8e687 b8e746
            | exact resolve b8e746 b8e687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e687 b8e746
          have b8e890 : x = y ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e872
               have r₂ := b8e21
               grind)
            | exact resolve b8e872 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e872
          have b8e891 : y = (M.op x y) := by
            first
            | (have r₁ := b8e890
               have r₂ := b8e22
               grind)
            | exact resolve b8e890 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e890
          have b8e950 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op (M.op (M.op X0 x) y) x) := by
            intro X0
            first
            | (have i₁ := b8e39 x x y
               have i₂ := b8e891
               grind)
            | exact superpose b8e891 b8e39
            | exact resolve b8e39 b8e891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e5876 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e171 (σ x) y
               have i₂ := b8e542
               grind)
            | exact superpose b8e542 b8e171
            | exact resolve b8e171 b8e542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171
          have b8e5958 : x = y ∨ (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
            first
            | (have i₁ := b8e5876
               have i₂ := b8e891
               grind)
            | exact superpose b8e891 b8e5876
            | exact resolve b8e5876 b8e891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5876
          have b8e5976 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
            first
            | (have r₁ := b8e5958
               have r₂ := b8e22
               grind)
            | exact resolve b8e5958 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5958
          have b8e6357 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e5976
               have i₂ := b8e542
               grind)
            | exact superpose b8e542 b8e5976
            | exact resolve b8e5976 b8e542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e542 b8e5976
          have b8e6388 : x = (k x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e6357
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e6357
            | exact resolve b8e6357 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6357
          have b8e6400 : x = y ∨ x = (k x y) := by
            first
            | (have i₁ := b8e6388
               have i₂ := b8e891
               grind)
            | exact superpose b8e891 b8e6388
            | exact resolve b8e6388 b8e891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6388
          have b8e6412 : x = (k x y) := by
            first
            | (have r₁ := b8e6400
               have r₂ := b8e22
               grind)
            | exact resolve b8e6400 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6400
          have b8e6465 : x = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e18 x y
               have i₂ := b8e6412
               grind)
            | exact superpose b8e6412 b8e18
            | (have j0 := b8e18 x y
               grind)
            | exact resolve b8e18 b8e6412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6412
          have b8e6484 : x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e6465
               have r₂ := b8e22
               grind)
            | exact resolve b8e6465 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6465
          have b8e6494 : x = (M.op y x) := by
            first
            | (have r₁ := b8e6484
               have r₂ := b8e21
               grind)
            | exact resolve b8e6484 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6484
          have b8e6795 : (M.op x y) = (M.op (M.op x y) x) := by
            first
            | (have i₁ := b8e950 y
               have i₂ := b8e6494
               grind)
            | exact superpose b8e6494 b8e950
            | exact resolve b8e950 b8e6494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e950 b8e6494
          have b8e6844 : y = (M.op y x) := by
            first
            | (have i₁ := b8e6795
               have i₂ := b8e891
               grind)
            | exact superpose b8e891 b8e6795
            | exact resolve b8e6795 b8e891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e891 b8e6795
          have b8e6855 : False := by grind
          exact b8e6855

/-- `Equation839`: `x = x ◇ ((y ◇ x) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_pyx_pxy_Equation839 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law839 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law839.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e39 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
           have i₂ := b0e11 (M.op (M.op X0 X1) X2) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e83 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 (M.op (M.op x x) X0) X1
           have i₂ := b0e39 x x X0
           grind)
        | exact superpose b0e39 b0e39
        | exact resolve b0e39 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e115 : x = (M.op x y) := by
        first
        | (have i₁ := b0e83 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e83
        | exact resolve b0e83 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e118 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e83 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e83
        | exact resolve b0e83 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e266 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e118
           grind)
        | exact superpose b0e118 b0e18
        | exact resolve b0e18 b0e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118
      have b0e279 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e266
           have i₂ := b0e115
           grind)
        | exact superpose b0e115 b0e266
        | exact resolve b0e266 b0e115
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e115 b0e266
      have b0e280 : False := by grind
      exact b0e280
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b1e24 : x = (k x y) := by grind
        have b1e39 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e42 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e39
        have b1e44 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e42
             have r₂ := b1e21
             grind)
          | exact resolve b1e42 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e45 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e44
          | exact resolve b1e44 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e46 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e45
          | exact resolve b1e45 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e45
        have b1e47 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e46
             grind)
          | exact superpose b1e46 b1e19
          | exact resolve b1e19 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e46
             grind)
          | exact superpose b1e46 b1e22
          | exact resolve b1e22 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e46
             grind)
          | exact superpose b1e46 b1e13
          | exact resolve b1e13 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : x = y := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e51
          | exact resolve b1e51 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e55 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e48
             grind)
          | exact superpose b1e48 b1e47
          | exact resolve b1e47 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e48
        have b1e56 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e52
             grind)
          | exact superpose b1e52 b1e55
          | exact resolve b1e55 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e55
        have b1e57 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e56
          | exact resolve b1e56 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e58 : False := by grind
        exact b1e58
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
          intro X0 X1 X2
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
        have b2e31 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
             have i₂ := b2e12 (M.op (M.op X0 X1) X2) X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e71 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X0 (M.op (M.op x x) X0) X1
             have i₂ := b2e31 x x X0
             grind)
          | exact superpose b2e31 b2e31
          | exact resolve b2e31 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e226 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e54 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e227 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e226
             have r₂ := b2e22
             grind)
          | exact resolve b2e226 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e226
        have b2e228 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e227
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e227
          | exact resolve b2e227 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e227
        have b2e229 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e228
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e228
          | exact resolve b2e228 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e228
        have b2e237 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e71 (σ x) (σ y)
             have i₂ := b2e229
             grind)
          | exact superpose b2e229 b2e71
          | exact resolve b2e71 b2e229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71 b2e229
        have b2e239 : False := by grind
        exact b2e239
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b3e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e24
          | exact resolve b3e24 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e26 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e25
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : x = (k x y) := by
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
        have b3e52 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e53 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e52
        have b3e56 : y = (k x y) := by
          first
          | (have r₁ := b3e53
             have r₂ := b3e20
             grind)
          | exact resolve b3e53 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e57 : x = y := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e56
          | exact resolve b3e56 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e56
        have b3e59 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e19
          | exact resolve b3e19 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e62 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e21
          | exact resolve b3e21 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e63 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e59
          | exact resolve b3e59 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e62
        have b3e64 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e63
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e65 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e64
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e64
          | exact resolve b3e64 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e64
        have b3e66 : False := by grind
        exact b3e66
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b4e13 x y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 : G, (M.op X0 (M.op (M.op x X0) y)) = X0 := by
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
          have b4e34 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
               have i₂ := b4e13 (M.op (M.op X0 X1) X2) X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : x = (M.op x y) := by
            first
            | (have i₁ := b4e28 (M.op x y)
               have i₂ := b4e31 y
               grind)
            | exact superpose b4e31 b4e28
            | exact resolve b4e28 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e31
          have b4e73 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X0 (M.op (M.op x x) X0) X1
               have i₂ := b4e34 x x X0
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e134 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e73 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e73
            | exact resolve b4e73 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e334 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e134
               grind)
            | exact superpose b4e134 b4e20
            | exact resolve b4e20 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e348 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e334
               have i₂ := b4e63
               grind)
            | exact superpose b4e63 b4e334
            | exact resolve b4e334 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63 b4e334
          have b4e349 : False := by grind
          exact b4e349
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b5e13 x y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op X0 (M.op (M.op x X0) y)) = X0 := by
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
          have b5e32 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
               have i₂ := b5e13 (M.op (M.op X0 X1) X2) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : y ≠ y ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X0) (M.op X2 X1)) (M.op (M.op X1 X0) (M.op X2 X1))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 (M.op (M.op X1 X0) (M.op X2 X1)) X0
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 (M.op (M.op X1 X0) (M.op X2 X1)) X0
               grind)
            | (have r₁ := b5e17 (M.op (M.op X1 X0) (M.op X2 X1)) X0
               have r₂ := b5e13 X0 X1 X2
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op y (M.op X0 y)) (M.op y (M.op X0 y))) ∨ x = (k (M.op y (M.op X0 y)) x) := by
            intro X0
            first
            | (have i₁ := b5e17 (M.op y (M.op X0 y)) x
               have i₂ := b5e28 X0
               grind)
            | exact superpose b5e28 b5e17
            | (have j0 := b5e17 (M.op y (M.op X0 y)) x
               grind)
            | (have r₁ := b5e17 (M.op y (M.op X0 y)) x
               have r₂ := b5e28 X0
               grind)
            | exact resolve b5e17 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 y)) (M.op y (M.op X0 y))) ∨ x = (k (M.op y (M.op X0 y)) x) := by
            intro X0
            first
            | (have j0 := b5e37 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e39 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) (M.op (M.op X1 X0) (M.op X2 X1))) = X0 ∨ (k (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e36 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e40 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e35
          have b5e41 : y = (k x y) := by
            first
            | (have r₁ := b5e40
               have r₂ := b5e21
               grind)
            | exact resolve b5e40 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e52 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e53 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op y (M.op X0 y)) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op y (M.op X0 y))
               have i₂ := b5e28 X0
               grind)
            | exact superpose b5e28 b5e30
            | exact resolve b5e30 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : x = (M.op x y) := by
            first
            | (have i₁ := b5e28 (M.op x y)
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e28
            | exact resolve b5e28 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e30
          have b5e64 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op y (M.op X0 y)) x) := by
            intro X0
            first
            | (have i₁ := b5e53 X0
               have i₂ := b5e57
               grind)
            | exact superpose b5e57 b5e53
            | exact resolve b5e53 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e68 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e32 X0 (M.op (M.op x x) X0) X1
               have i₂ := b5e32 x x X0
               grind)
            | exact superpose b5e32 b5e32
            | exact resolve b5e32 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e47 (σ X1) (σ X0)
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e47
            | (have j0 := b5e47 (σ X1) (σ X0)
               grind)
            | exact resolve b5e47 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e272 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e52 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e273 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e272
               have r₂ := b5e24
               grind)
            | exact resolve b5e272 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e272
          have b5e274 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e273
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e273
            | exact resolve b5e273 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e273
          have b5e275 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e274
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e274
            | exact resolve b5e274 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e274
          have b5e276 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e275
               grind)
            | exact superpose b5e275 b5e20
            | exact resolve b5e20 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e283 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e68 (σ x) (σ y)
               have i₂ := b5e275
               grind)
            | exact superpose b5e275 b5e68
            | exact resolve b5e68 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e285 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e276
               have i₂ := b5e57
               grind)
            | exact superpose b5e57 b5e276
            | exact resolve b5e276 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57 b5e276
          have b5e488 : (σ y) = (k (σ y) (σ y)) := by grind
          have b5e504 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e488
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e488
            | exact resolve b5e488 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e488
          have b5e577 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e504
               grind)
            | exact superpose b5e504 b5e14
            | exact resolve b5e14 b5e504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e504
          have b5e579 : y = (k y y) := by
            first
            | (have i₁ := b5e577
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e577
            | exact resolve b5e577 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e577
          have b5e589 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e579
               grind)
            | exact superpose b5e579 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e579
          have b5e590 : y = (M.op y y) := by grind
          clear b5e589
          have b5e638 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ X1) X2) (σ (k X0 X1)))) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (σ X1) (σ X0)
               have i₂ := b5e45 X0 X1
               grind)
            | exact superpose b5e45 b5e13
            | (have j1 := b5e45 X0 X1
               grind)
            | exact resolve b5e13 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e1546 : ∀ X0 X1 : G, x = (M.op (M.op (M.op y (M.op X0 y)) (M.op X1 (M.op y (M.op X0 y)))) (M.op (M.op y (M.op X0 y)) (M.op X1 (M.op y (M.op X0 y))))) ∨ x = (k (M.op (M.op y (M.op X0 y)) (M.op X1 (M.op y (M.op X0 y)))) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e39 x (M.op y (M.op X0 y)) x
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e39
            | exact resolve b5e39 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e64
          have b5e1556 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X0 y)) (M.op y (M.op X0 y))) ∨ x = (k (M.op (M.op y (M.op X0 y)) (M.op X1 (M.op y (M.op X0 y)))) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e1546 X0 X0
               have i₂ := b5e68 X0 (M.op y (M.op X0 y))
               grind)
            | exact superpose b5e68 b5e1546
            | (have j0 := b5e1546 X0 X1
               grind)
            | exact resolve b5e1546 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1546
          have b5e1567 : ∀ X0 X1 : G, x = (M.op y y) ∨ x = (k (M.op (M.op y (M.op X0 y)) (M.op X1 (M.op y (M.op X0 y)))) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e1556 X0 X1
               have i₂ := b5e68 X0 y
               grind)
            | exact superpose b5e68 b5e1556
            | (have j0 := b5e1556 X0 X1
               grind)
            | exact resolve b5e1556 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1556
          have b5e1571 : ∀ X0 X1 : G, x = y ∨ x = (k (M.op (M.op y (M.op X0 y)) (M.op X1 (M.op y (M.op X0 y)))) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e1567 X0 X1
               have i₂ := b5e590
               grind)
            | exact superpose b5e590 b5e1567
            | (have j0 := b5e1567 X0 X1
               grind)
            | exact resolve b5e1567 b5e590
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e590 b5e1567
          have b5e1573 : ∀ X0 : G, x = (k (M.op y (M.op X0 y)) x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e1571 X0 x
               have i₂ := b5e68 x (M.op y (M.op X0 y))
               grind)
            | exact superpose b5e68 b5e1571
            | exact resolve b5e1571 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1571
          have b5e1574 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b5e1573 x
               have i₂ := b5e68 x y
               grind)
            | exact superpose b5e68 b5e1573
            | exact resolve b5e1573 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1573
          have b5e10126 : ∀ X0 : G, (M.op y (M.op X0 y)) = (k (M.op y (M.op X0 y)) x) ∨ x = (k (M.op y (M.op X0 y)) x) := by
            intro X0
            grind
          clear b5e38
          have b5e10215 : ∀ X0 : G, y = (k y x) ∨ x = (k (M.op y (M.op X0 y)) x) := by
            intro X0
            first
            | (have i₁ := b5e10126 X0
               have i₂ := b5e68 X0 y
               grind)
            | exact superpose b5e68 b5e10126
            | (have j0 := b5e10126 X0
               grind)
            | exact resolve b5e10126 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10126
          have b5e10239 : y = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b5e10215 x
               have i₂ := b5e68 x y
               grind)
            | exact superpose b5e68 b5e10215
            | exact resolve b5e10215 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68 b5e10215
          have b5e10264 : x ≠ y ∨ x = (k y x) := by grind
          clear b5e10239
          have b5e10266 : x = (k y x) := by
            first
            | (have r₁ := b5e10264
               have r₂ := b5e1574
               grind)
            | exact resolve b5e10264 b5e1574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1574 b5e10264
          have b5e28300 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) X0) (σ x))) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e638 y x X0
               have i₂ := b5e10266
               grind)
            | exact superpose b5e10266 b5e638
            | (have j0 := b5e638 y x x
               grind)
            | exact resolve b5e638 b5e10266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e638
          have b5e28820 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (M.op (M.op (σ x) X0) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e28300 X0
               have i₂ := b5e283
               grind)
            | exact superpose b5e283 b5e28300
            | (have j0 := b5e28300 X0
               grind)
            | exact resolve b5e28300 b5e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e283 b5e28300
          have b5e28837 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) X0) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e28820 X0
               grind)
            | (have r₁ := b5e28820 X0
               have r₂ := b5e285
               grind)
            | exact resolve b5e28820 b5e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28820
          have b5e28843 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (M.op (M.op (σ x) X0) (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e28837 X0
               have i₂ := b5e275
               grind)
            | exact superpose b5e275 b5e28837
            | (have j0 := b5e28837 X0
               grind)
            | exact resolve b5e28837 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28837
          have b5e28848 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) X0) (σ x))) = X0 := by
            intro X0
            first
            | (have j0 := b5e28843 X0
               grind)
            | (have r₁ := b5e28843 X0
               have r₂ := b5e285
               grind)
            | exact resolve b5e28843 b5e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28843
          have b5e28853 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e28848 (σ y)
               have i₂ := b5e275
               grind)
            | exact superpose b5e275 b5e28848
            | exact resolve b5e28848 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28848
          have b5e29537 : (σ y) = (M.op (σ y) (σ (k y x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b5e28853
               have i₂ := b5e227 y x
               grind)
            | exact superpose b5e227 b5e28853
            | (have j1 := b5e227 y x
               grind)
            | exact resolve b5e28853 b5e227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e227 b5e28853
          have b5e29676 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b5e29537
               have i₂ := b5e10266
               grind)
            | exact superpose b5e10266 b5e29537
            | exact resolve b5e29537 b5e10266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29537
          have b5e29682 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b5e29676
               have r₂ := b5e24
               grind)
            | exact resolve b5e29676 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29676
          have b5e29684 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b5e29682
               have i₂ := b5e275
               grind)
            | exact superpose b5e275 b5e29682
            | exact resolve b5e29682 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e275 b5e29682
          have b5e29686 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b5e29684
               have r₂ := b5e285
               grind)
            | exact resolve b5e29684 b5e285
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29684
          have b5e29687 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e29686
               have i₂ := b5e10266
               grind)
            | exact superpose b5e10266 b5e29686
            | exact resolve b5e29686 b5e10266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10266 b5e29686
          have b5e29688 : False := by grind
          exact b5e29688
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
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
        have b6e44 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
             have i₂ := b6e12 (M.op (M.op X0 X1) X2) X1 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e47 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e44 X0 (M.op (M.op x x) X0) X1
             have i₂ := b6e44 x x X0
             grind)
          | exact superpose b6e44 b6e44
          | exact resolve b6e44 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e74 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e86 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e74
             have r₂ := b6e20
             grind)
          | exact resolve b6e74 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e89 : x = (M.op x y) := by
          first
          | (have r₁ := b6e86
             have r₂ := b6e21
             grind)
          | exact resolve b6e86 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e91 : y = (M.op y x) := by
          first
          | (have i₁ := b6e47 x y
             have i₂ := b6e89
             grind)
          | exact superpose b6e89 b6e47
          | exact resolve b6e47 b6e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47 b6e89
        have b6e98 : False := by grind
        exact b6e98
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) := by
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
          have b7e32 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
               have i₂ := b7e13 (M.op (M.op X0 X1) X2) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e32 X0 (M.op (M.op x x) X0) X1
               have i₂ := b7e32 x x X0
               grind)
            | exact superpose b7e32 b7e32
            | exact resolve b7e32 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e40 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e45 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e46 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : y = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e57 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e47
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e47 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e66 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e21
               grind)
            | exact resolve b7e57 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e67 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e22
               grind)
            | exact resolve b7e66 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e69 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e70 : y = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e21
               grind)
            | exact resolve b7e69 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e72 : y = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e22
               grind)
            | exact resolve b7e70 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e83 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) y)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e13
            | exact resolve b7e13 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e35 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e99 : y = (M.op y y) := by
            first
            | (have i₁ := b7e35 x y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e35
            | exact resolve b7e35 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e125 : y = (k y y) := by grind
          clear b7e99
          have b7e137 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (M.op (σ y) (M.op X0 (σ y))) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (k (M.op (σ y) (M.op X0 (σ y))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e17 (M.op (σ y) (M.op X0 (σ y))) (σ x)
               have i₂ := b7e28 X0
               grind)
            | exact superpose b7e28 b7e17
            | (have j0 := b7e17 (M.op (σ y) (M.op X0 (σ y))) (σ x)
               grind)
            | (have r₁ := b7e17 (M.op (σ y) (M.op X0 (σ y))) (σ x)
               have r₂ := b7e28 X0
               grind)
            | exact resolve b7e17 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e141 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 (σ y))) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (k (M.op (σ y) (M.op X0 (σ y))) (σ x)) := by
            intro X0
            first
            | (have j0 := b7e137 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e137
          have b7e144 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (M.op (σ y) (M.op X0 (σ y))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e141 X0
               have i₂ := b7e35 X0 (σ y)
               grind)
            | exact superpose b7e35 b7e141
            | (have j0 := b7e141 X0
               grind)
            | exact resolve b7e141 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141
          have b7e148 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e144 x
               have i₂ := b7e35 x (σ y)
               grind)
            | exact superpose b7e35 b7e144
            | exact resolve b7e144 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e144
          have b7e150 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e148
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e148
            | exact resolve b7e148 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e148
          have b7e230 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e20
            | exact resolve b7e20 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e244 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e230
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e230
            | exact resolve b7e230 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e230
          have b7e1787 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e56 y y
               have i₂ := b7e150
               grind)
            | exact superpose b7e150 b7e56
            | exact resolve b7e56 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e150
          have b7e1810 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
          clear b7e1787
          have b7e1817 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b7e1810
               have r₂ := b7e244
               grind)
            | exact resolve b7e1810 b7e244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1810
          have b7e1821 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1817
               have i₂ := b7e125
               grind)
            | exact superpose b7e125 b7e1817
            | exact resolve b7e1817 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125 b7e1817
          have b7e1824 : (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b7e1821
               have r₂ := b7e244
               grind)
            | exact resolve b7e1821 b7e244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1821
          have b7e1831 : (k y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e1824
               grind)
            | exact superpose b7e1824 b7e14
            | exact resolve b7e14 b7e1824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1824
          have b7e1862 : x = (k y x) := by
            first
            | (have i₁ := b7e1831
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1831
            | exact resolve b7e1831 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1831
          have b7e2005 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e58 x y
               have i₂ := b7e1862
               grind)
            | exact superpose b7e1862 b7e58
            | (have j0 := b7e58 x y
               grind)
            | exact resolve b7e58 b7e1862
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e1862
          have b7e2008 : x = y ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e2005
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e2005
            | exact resolve b7e2005 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2005
          have b7e2009 : x = (M.op y x) ∨ x = y := by grind
          clear b7e2008
          have b7e2168 : x = (M.op x (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b7e83 x
               have i₂ := b7e2009
               grind)
            | exact superpose b7e2009 b7e83
            | exact resolve b7e83 b7e2009
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e2009
          have b7e2189 : x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e2168
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e2168
            | exact resolve b7e2168 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2168
          have b7e2190 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e2189
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e2189
            | exact resolve b7e2189 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e2189
          have b7e2191 : x = y := by grind
          clear b7e2190
          have b7e2454 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b7e244
               have i₂ := b7e2191
               grind)
            | exact superpose b7e2191 b7e244
            | exact resolve b7e244 b7e2191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e244 b7e2191
          have b7e2458 : False := by grind
          exact b7e2458
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e30 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
               have i₂ := b8e13 (M.op (M.op X0 X1) X2) X1 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X0 (M.op (M.op x x) X0) X1
               have i₂ := b8e30 x x X0
               grind)
            | exact superpose b8e30 b8e30
            | exact resolve b8e30 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e43 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 (M.op X1 X0)
               have i₂ := b8e32 X1 X0
               grind)
            | exact superpose b8e32 b8e32
            | exact resolve b8e32 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e66 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e43 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e43 X0 X1
               have i₂ := b8e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b8e18 b8e43
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e43 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e76 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e66 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e544 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e53 x y
               grind)
            | exact superpose b8e53 b8e24
            | (have j1 := b8e53 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e53 x y
               grind)
            | exact resolve b8e24 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e565 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
          clear b8e544
          have b8e582 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e565
               have r₂ := b8e23
               grind)
            | exact resolve b8e565 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e565
          have b8e595 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e582
               grind)
            | exact superpose b8e582 b8e20
            | exact resolve b8e20 b8e582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e582
          have b8e648 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e595
               have i₂ := b8e76 y x
               grind)
            | exact superpose b8e76 b8e595
            | (have j1 := b8e76 y x
               grind)
            | exact resolve b8e595 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e595
          have b8e653 : y = (M.op y x) := by grind
          clear b8e648
          have b8e658 : False := by grind
          exact b8e658

/-- `Equation839`: `x = x ◇ ((y ◇ x) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_x_pxx_pxy_Equation839 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law839 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law839.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : x = y := by
          first
          | (have i₁ := b1e27
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e27
          | exact resolve b1e27 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e29 : y = (M.op y y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e20
          | exact resolve b1e20 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e29
             grind)
          | exact superpose b1e29 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 y y
             have r₂ := b1e29
             grind)
          | exact resolve b1e15 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e32 : y = (k y y) := by grind
        clear b1e31
        have b1e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e209 : (M.op (σ y) (σ y)) = (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e65 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e65
          | (have j0 := b1e65 y
             grind)
          | exact resolve b1e65 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e223 : (M.op (σ y) (σ y)) = (σ (k x x)) := by
          first
          | (have r₁ := b1e209
             have r₂ := b1e24
             grind)
          | exact resolve b1e209 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e209
        have b1e226 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e223
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e223
          | exact resolve b1e223 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e223
        have b1e228 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e226
             have i₂ := b1e32
             grind)
          | exact superpose b1e32 b1e226
          | exact resolve b1e226 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e226
        have b1e229 : False := by grind
        exact b1e229
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : y ≠ y ∨ x = (k x y) := by
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
        have b2e26 : x = (k x y) := by grind
        clear b2e25
        have b2e35 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) y)) = X0 := by
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
        have b2e37 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
             have i₂ := b2e12 (M.op (M.op X0 X1) X2) X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 : G, (M.op X0 (M.op y X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y (M.op y (M.op y X0))
             have i₂ := b2e35 (M.op y X0)
             grind)
          | exact superpose b2e35 b2e12
          | exact resolve b2e12 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e71 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e37 X0 (M.op y X0) X1
             have i₂ := b2e52 X0
             grind)
          | exact superpose b2e52 b2e37
          | exact resolve b2e37 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e52
        have b2e84 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op (M.op y X0) y) X0) := by
          intro X0
          first
          | (have i₁ := b2e71 X0 (M.op (M.op y X0) y)
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e71
          | exact resolve b2e71 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e443 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X1) (σ X0) X2
             have i₂ := b2e55 X0 X1
             grind)
          | exact superpose b2e55 b2e12
          | (have j1 := b2e55 X0 X1
             grind)
          | exact resolve b2e12 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17786 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e443 x y X0
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e443
          | (have j0 := b2e443 x y x
             grind)
          | exact resolve b2e443 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e443
        have b2e17933 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e17786 X0
             grind)
          | (have r₁ := b2e17786 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e17786 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17786
        have b2e17944 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have j0 := b2e17933 X0
             grind)
          | (have r₁ := b2e17933 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e17933 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17933
        have b2e17948 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e17944 x
             have i₂ := b2e71 x (σ x)
             grind)
          | exact superpose b2e71 b2e17944
          | exact resolve b2e17944 b2e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17944
        have b2e17956 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e55 y x
             have i₂ := b2e17948
             grind)
          | exact superpose b2e17948 b2e55
          | (have j0 := b2e55 y (k y x)
             grind)
          | exact resolve b2e55 b2e17948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e17948
        have b2e18034 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
        clear b2e17956
        have b2e18068 : (σ y) = (σ (k y x)) := by
          first
          | (have r₁ := b2e18034
             have r₂ := b2e22
             grind)
          | exact resolve b2e18034 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18034
        have b2e18310 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b2e13 (k y x)
             have i₂ := b2e18068
             grind)
          | exact superpose b2e18068 b2e13
          | exact resolve b2e13 b2e18068
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18068
        have b2e18355 : y = (k y x) := by
          first
          | (have i₁ := b2e18310
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e18310
          | exact resolve b2e18310 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18310
        have b2e18538 : x = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e17 y x
             have i₂ := b2e18355
             grind)
          | exact superpose b2e18355 b2e17
          | (have j0 := b2e17 x (M.op y x)
             grind)
          | exact resolve b2e17 b2e18355
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e18355
        have b2e22650 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e84 x
             have i₂ := b2e18538
             grind)
          | exact superpose b2e18538 b2e84
          | exact resolve b2e84 b2e18538
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84 b2e18538
        have b2e22770 : y = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b2e22650
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e22650
          | exact resolve b2e22650 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22650
        have b2e22771 : y = (M.op y x) ∨ x = y := by grind
        clear b2e22770
        have b2e22920 : x = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b2e71 y x
             have i₂ := b2e22771
             grind)
          | exact superpose b2e22771 b2e71
          | exact resolve b2e71 b2e22771
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71 b2e22771
        have b2e23004 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e22920
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e22920
          | exact resolve b2e22920 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e22920
        have b2e23005 : x = y := by grind
        clear b2e23004
        have b2e23170 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e23005
             grind)
          | exact superpose b2e23005 b2e22
          | exact resolve b2e22 b2e23005
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23005
        have b2e23204 : False := by grind
        exact b2e23204
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
        have b3e29 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e28
        have b3e30 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e29
          | exact resolve b3e29 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e32 : y = (k y y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e55 : y = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e32
        have b3e58 : y = (M.op y y) := by grind
        clear b3e55
        have b3e61 : False := by grind
        exact b3e61
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x y) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e137 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e44
          have b4e148 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e137
          have b4e151 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e148
          have b4e152 : y = (M.op y y) := by grind
          clear b4e151
          have b4e153 : False := by grind
          exact b4e153
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ y := by grind
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
        have b6e25 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e26 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e25
        have b6e27 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e26
          | exact resolve b6e26 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b6e32 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e27
             grind)
          | exact superpose b6e27 b6e13
          | exact resolve b6e13 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e33 : x = (k x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e32
          | exact resolve b6e32 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e38 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (σ y))) = X0 := by
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
        have b6e40 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
             have i₂ := b6e12 (M.op (M.op X0 X1) X2) X1 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e46 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X0 (M.op (M.op x x) X0) X1
             have i₂ := b6e40 x x X0
             grind)
          | exact superpose b6e40 b6e40
          | exact resolve b6e40 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e55 : x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e33
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e33 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e58 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e55
             have r₂ := b6e21
             grind)
          | exact resolve b6e55 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e61 : x = (M.op x y) := by
          first
          | (have r₁ := b6e58
             have r₂ := b6e20
             grind)
          | exact resolve b6e58 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e63 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e61
             grind)
          | exact superpose b6e61 b6e24
          | exact resolve b6e24 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e72 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e28 X0 X1
             have i₂ := b6e17 (τ X0) X1
             grind)
          | exact superpose b6e17 b6e28
          | (have j1 := b6e17 (τ X0) X1
             grind)
          | exact resolve b6e28 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e84 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e29 X1 X0
             grind)
          | exact superpose b6e29 b6e13
          | exact resolve b6e13 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e107 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e46 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e46
          | exact resolve b6e46 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e113 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 (M.op X1 X0)
             have i₂ := b6e46 X1 X0
             grind)
          | exact superpose b6e46 b6e15
          | (have j0 := b6e15 X1 X0
             grind)
          | exact resolve b6e15 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e429 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k y X0)) (σ y))) ∨ (σ X0) = (σ y) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e38 (σ X0)
             have i₂ := b6e54 y X0
             grind)
          | exact superpose b6e54 b6e38
          | (have j1 := b6e54 X0 y
             grind)
          | exact resolve b6e38 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e6190 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e72 X0 (M.op X0 (τ X0))
             have i₂ := b6e46 X0 (τ X0)
             grind)
          | exact superpose b6e46 b6e72
          | (have j0 := b6e72 X0 (M.op X1 (τ X0))
             grind)
          | exact resolve b6e72 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46 b6e72
        have b6e6208 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) := by
          intro X0 X1
          first
          | (have j0 := b6e6190 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6190
        have b6e6239 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e6208 X0 X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e6208
          | (have j0 := b6e6208 X0 X1
             grind)
          | exact resolve b6e6208 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6208
        have b6e10807 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e84 X0 (σ (M.op X1 (τ (σ X0))))
             have i₂ := b6e6239 (σ X0) X1
             grind)
          | exact superpose b6e6239 b6e84
          | (have j1 := b6e6239 (σ X0) X1
             grind)
          | exact resolve b6e84 b6e6239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e6239
        have b6e10821 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e10807 X0 X1
             have i₂ := b6e13 (M.op X1 (τ (σ X0)))
             grind)
          | exact superpose b6e13 b6e10807
          | (have j0 := b6e10807 X0 X1
             grind)
          | exact resolve b6e10807 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10807
        have b6e10839 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b6e10821 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e10821
          | (have j0 := b6e10821 X0 X1
             grind)
          | exact resolve b6e10821 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10821
        have b6e10850 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e10839 X0 X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e10839
          | (have j0 := b6e10839 X0 X1
             grind)
          | exact resolve b6e10839 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10839
        have b6e10857 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e10850 X0 X1
             have j1 := b6e113 X0 X1
             grind)
          | (have r₁ := b6e10850 X0 X1
             have r₂ := b6e113 X0 X1
             grind)
          | exact resolve b6e10850 b6e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e113 b6e10850
        have b6e11244 : y = (k y x) := by
          first
          | (have i₁ := b6e10857 y x
             have i₂ := b6e61
             grind)
          | exact superpose b6e61 b6e10857
          | exact resolve b6e10857 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e10857
        have b6e13207 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e429 x
             have i₂ := b6e11244
             grind)
          | exact superpose b6e11244 b6e429
          | (have j0 := b6e429 x
             grind)
          | exact resolve b6e429 b6e11244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e429 b6e11244
        have b6e13309 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b6e13207
             have r₂ := b6e63
             grind)
          | exact resolve b6e13207 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13207
        have b6e13319 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e13309
             have i₂ := b6e107
             grind)
          | exact superpose b6e107 b6e13309
          | exact resolve b6e13309 b6e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e107 b6e13309
        have b6e13324 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e13319
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13319
          | exact resolve b6e13319 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13319
        have b6e13327 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b6e13324
             have r₂ := b6e63
             grind)
          | exact resolve b6e13324 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13324
        have b6e13331 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b6e38 (σ x)
             have i₂ := b6e13327
             grind)
          | exact superpose b6e13327 b6e38
          | exact resolve b6e38 b6e13327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e13327
        have b6e13434 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e13331
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13331
          | exact resolve b6e13331 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13331
        have b6e13436 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13434
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13434
          | exact resolve b6e13434 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13434
        have b6e13438 : False := by grind
        exact b6e13438
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e351 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e51 x y
               grind)
            | exact superpose b8e51 b8e20
            | (have j1 := b8e51 x y
               grind)
            | exact resolve b8e20 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e370 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e351
               have r₂ := b8e24
               grind)
            | exact resolve b8e351 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e351
          have b8e373 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e370
               have r₂ := b8e23
               grind)
            | exact resolve b8e370 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e370
          have b8e374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e373
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e373
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e373
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e373
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e373 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e373
          have b8e375 : x = y ∨ y = (M.op x y) := by grind
          clear b8e374
          have b8e376 : y = (M.op x y) := by
            first
            | (have r₁ := b8e375
               have r₂ := b8e22
               grind)
            | exact resolve b8e375 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e375
          have b8e377 : False := by grind
          exact b8e377

/-- `Equation839`: `x = x ◇ ((y ◇ x) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_x_pxx_pyx_Equation839 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law839 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law839.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b0e11 x y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op X0 (M.op (M.op x X0) y)) = X0 := by
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
      have b0e39 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
           have i₂ := b0e11 (M.op (M.op X0 X1) X2) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : x = (M.op x y) := by
        first
        | (have i₁ := b0e33 (M.op x y)
           have i₂ := b0e36 y
           grind)
        | exact superpose b0e36 b0e33
        | exact resolve b0e33 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e36
      have b0e76 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 (M.op (M.op x x) X0) X1
           have i₂ := b0e39 x x X0
           grind)
        | exact superpose b0e39 b0e39
        | exact resolve b0e39 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e142 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e76 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e76
        | exact resolve b0e76 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e628 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e142
           grind)
        | exact superpose b0e142 b0e18
        | exact resolve b0e18 b0e142
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142
      have b0e653 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e628
           have i₂ := b0e57
           grind)
        | exact superpose b0e57 b0e628
        | exact resolve b0e628 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57 b0e628
      have b0e654 : False := by grind
      exact b0e654
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e28 : y = (M.op y y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e20
          | exact resolve b1e20 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 y y
             have r₂ := b1e28
             grind)
          | exact resolve b1e15 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e31 : y = (k y y) := by grind
        clear b1e30
        have b1e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e289 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e64 y
             grind)
          | exact superpose b1e64 b1e25
          | (have j1 := b1e64 y
             grind)
          | exact resolve b1e25 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e64
        have b1e307 : (σ (M.op x y)) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e289
             have r₂ := b1e24
             grind)
          | exact resolve b1e289 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e289
        have b1e311 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e307
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e307
          | exact resolve b1e307 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e307
        have b1e314 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e311
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e311
          | exact resolve b1e311 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e311
        have b1e316 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e314
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e314
          | exact resolve b1e314 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e314
        have b1e317 : False := by grind
        exact b1e317
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
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
        have b2e28 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b2e12 x y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, (M.op X0 (M.op (M.op x X0) y)) = X0 := by
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
        have b2e32 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
             have i₂ := b2e12 (M.op (M.op X0 X1) X2) X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : x = (M.op x y) := by
          first
          | (have i₁ := b2e28 (M.op x y)
             have i₂ := b2e30 y
             grind)
          | exact superpose b2e30 b2e28
          | exact resolve b2e28 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e30
        have b2e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e48
             grind)
          | exact superpose b2e48 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e48
             grind)
          | exact resolve b2e15 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e62 : y = (k y x) := by grind
        clear b2e61
        have b2e67 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 (M.op (M.op x x) X0) X1
             have i₂ := b2e32 x x X0
             grind)
          | exact superpose b2e32 b2e32
          | exact resolve b2e32 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e448 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op X2 (σ X1)))) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X0) (σ X1) X2
             have i₂ := b2e56 X1 X0
             grind)
          | exact superpose b2e56 b2e12
          | (have j1 := b2e56 X0 X1
             grind)
          | exact resolve b2e12 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e459 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e67 (σ X1) (σ X0)
             have i₂ := b2e56 X1 X0
             grind)
          | exact superpose b2e56 b2e67
          | (have j1 := b2e56 X0 X1
             grind)
          | exact resolve b2e67 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e12971 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e448 x y X0
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e448
          | (have j0 := b2e448 x y x
             grind)
          | exact resolve b2e448 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e448
        have b2e13107 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have j0 := b2e12971 X0
             grind)
          | (have r₁ := b2e12971 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e12971 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12971
        have b2e13125 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have j0 := b2e13107 X0
             grind)
          | (have r₁ := b2e13107 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e13107 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13107
        have b2e113894 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e459 y x
             have i₂ := b2e62
             grind)
          | exact superpose b2e62 b2e459
          | (have j0 := b2e459 x y
             grind)
          | exact resolve b2e459 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e459
        have b2e114259 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b2e113894
             have r₂ := b2e22
             grind)
          | exact resolve b2e113894 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113894
        have b2e150376 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e67 (σ x) (σ y)
             have i₂ := b2e114259
             grind)
          | exact superpose b2e114259 b2e67
          | exact resolve b2e67 b2e114259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e114259
        have b2e150658 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b2e150376
             have r₂ := b2e21
             grind)
          | exact resolve b2e150376 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150376
        have b2e151256 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b2e13125 (σ y)
             have i₂ := b2e150658
             grind)
          | exact superpose b2e150658 b2e13125
          | exact resolve b2e13125 b2e150658
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13125 b2e150658
        have b2e157968 : (σ x) = (M.op (σ x) (σ (k y x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e151256
             have i₂ := b2e56 x y
             grind)
          | exact superpose b2e56 b2e151256
          | (have j1 := b2e56 x y
             grind)
          | exact resolve b2e151256 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56 b2e151256
        have b2e158315 : (σ x) = (M.op (σ x) (σ (k y x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e157968
             have r₂ := b2e22
             grind)
          | exact resolve b2e157968 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e157968
        have b2e158317 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e158315
             have i₂ := b2e62
             grind)
          | exact superpose b2e62 b2e158315
          | exact resolve b2e158315 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62 b2e158315
        have b2e158318 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e158317
        have b2e159489 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e67 (σ x) (σ y)
             have i₂ := b2e158318
             grind)
          | exact superpose b2e158318 b2e67
          | exact resolve b2e67 b2e158318
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67 b2e158318
        have b2e159802 : False := by grind
        exact b2e159802
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
        have b3e29 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e28
        have b3e30 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e29
          | exact resolve b3e29 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e13
          | exact resolve b3e13 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e32 : y = (k y y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e57 : y = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e32
        have b3e60 : y = (M.op y y) := by grind
        clear b3e57
        have b3e63 : False := by grind
        exact b3e63
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e197 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e46
          have b4e214 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e197
          have b4e217 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e214
          have b4e218 : y = (M.op y y) := by grind
          clear b4e217
          have b4e219 : False := by grind
          exact b4e219
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ y := by grind
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
        have b6e39 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
             have i₂ := b6e12 (M.op (M.op X0 X1) X2) X1 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e43 X0 (M.op (M.op x x) X0) X1
             have i₂ := b6e43 x x X0
             grind)
          | exact superpose b6e43 b6e43
          | exact resolve b6e43 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e59 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e48 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e48
          | exact resolve b6e48 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e74 : x = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
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
        have b6e77 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e74
             have r₂ := b6e21
             grind)
          | exact resolve b6e74 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e80 : x = (M.op y x) := by
          first
          | (have r₁ := b6e77
             have r₂ := b6e20
             grind)
          | exact resolve b6e77 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e85 : ∀ X0 : G, (M.op X0 (M.op (M.op x X0) x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e80
             grind)
          | exact superpose b6e80 b6e12
          | exact resolve b6e12 b6e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e135 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ y) (M.op X0 (σ y))) = (k (M.op (σ y) (M.op X0 (σ y))) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e15 (M.op (σ y) (M.op X0 (σ y))) (σ x)
             have i₂ := b6e39 X0
             grind)
          | exact superpose b6e39 b6e15
          | (have j0 := b6e15 (M.op (σ y) (M.op X0 (σ y))) (σ x)
             grind)
          | (have r₁ := b6e15 (M.op (σ y) (M.op X0 (σ y))) (σ x)
             have r₂ := b6e39 X0
             grind)
          | exact resolve b6e15 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e136 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (k (M.op (σ y) (M.op X0 (σ y))) (σ x)) := by
          intro X0
          first
          | (have j0 := b6e135 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e135
        have b6e137 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e136 x
             have i₂ := b6e48 x (σ y)
             grind)
          | exact superpose b6e48 b6e136
          | exact resolve b6e136 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48 b6e136
        have b6e142 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e137
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e137
          | exact resolve b6e137 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e137
        have b6e207 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e142
             grind)
          | exact superpose b6e142 b6e13
          | exact resolve b6e13 b6e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142
        have b6e208 : y = (k y x) := by
          first
          | (have i₁ := b6e207
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e207
          | exact resolve b6e207 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e207
        have b6e249 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e208
             grind)
          | exact superpose b6e208 b6e17
          | (have j0 := b6e17 y (M.op x y)
             grind)
          | exact resolve b6e17 b6e208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e208
        have b6e250 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e249
             have r₂ := b6e21
             grind)
          | exact resolve b6e249 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e249
        have b6e489 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e19
          | exact resolve b6e19 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e1286 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e489
             have i₂ := b6e250
             grind)
          | exact superpose b6e250 b6e489
          | exact resolve b6e489 b6e250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e250 b6e489
        have b6e1312 : y = (M.op x y) := by grind
        clear b6e1286
        have b6e1430 : y = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b6e85 y
             have i₂ := b6e1312
             grind)
          | exact superpose b6e1312 b6e85
          | exact resolve b6e85 b6e1312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85 b6e1312
        have b6e1457 : y = (M.op y x) := by
          first
          | (have i₁ := b6e1430
             have i₂ := b6e80
             grind)
          | exact superpose b6e80 b6e1430
          | exact resolve b6e1430 b6e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80 b6e1430
        have b6e1460 : False := by grind
        exact b6e1460
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e30 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 (M.op X0 X1) (M.op X1 (M.op (M.op X0 X1) X2))
               have i₂ := b8e13 (M.op (M.op X0 X1) X2) X1 X0
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X0 (M.op (M.op x x) X0) X1
               have i₂ := b8e30 x x X0
               grind)
            | exact superpose b8e30 b8e30
            | exact resolve b8e30 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e349 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 x y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e372 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e349
               have r₂ := b8e24
               grind)
            | exact resolve b8e349 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e349
          have b8e1240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e372
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e372
            | (have j1 := b8e18 (σ x) (M.op (σ x) (σ y))
               grind)
            | (have r₁ := b8e372
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e372
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e372 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e372
          have b8e1241 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e1240
          have b8e1242 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e1241
               have r₂ := b8e22
               grind)
            | exact resolve b8e1241 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1241
          have b8e1258 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e34 (σ x) (σ y)
               have i₂ := b8e1242
               grind)
            | exact superpose b8e1242 b8e34
            | exact resolve b8e34 b8e1242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1242
          have b8e1281 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1258
               have r₂ := b8e23
               grind)
            | exact resolve b8e1258 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1258
          have b8e1332 : y = (M.op y x) := by
            first
            | (have i₁ := b8e34 x y
               have i₂ := b8e1281
               grind)
            | exact superpose b8e1281 b8e34
            | exact resolve b8e34 b8e1281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e1281
          have b8e1353 : False := by grind
          exact b8e1353

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_x_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 y))) = X0 := by
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
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) = X0 := by
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
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
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
      have b0e38 : y = (M.op y (M.op x x)) := by
        first
        | (have i₁ := b0e32 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e99 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b0e33 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e33
        | exact resolve b0e33 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e170 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e34 X0 X0 x x
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e34
        | exact resolve b0e34 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e180 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e170 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e170
        | exact resolve b0e170 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e181 : y = (M.op y x) := by
        first
        | (have i₁ := b0e170 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e170
        | exact resolve b0e170 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e185 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op X0 X0)
           have i₂ := b0e170 X0
           grind)
        | exact superpose b0e170 b0e11
        | exact resolve b0e11 b0e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170
      have b0e232 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e181
           grind)
        | exact superpose b0e181 b0e11
        | exact resolve b0e11 b0e181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e181
      have b0e605 : x = (M.op x y) := by
        first
        | (have i₁ := b0e232 x
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e232
        | exact resolve b0e232 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e232
      have b0e3387 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b0e185 (σ x) (σ y)
           have i₂ := b0e99
           grind)
        | exact superpose b0e99 b0e185
        | exact resolve b0e185 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99 b0e185
      have b0e3414 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e3387
           have i₂ := b0e180
           grind)
        | exact superpose b0e180 b0e3387
        | exact resolve b0e3387 b0e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e180 b0e3387
      have b0e3715 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e3414
           grind)
        | exact superpose b0e3414 b0e18
        | exact resolve b0e18 b0e3414
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3414
      have b0e3733 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e3715
           have i₂ := b0e605
           grind)
        | exact superpose b0e605 b0e3715
        | exact resolve b0e3715 b0e605
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e605 b0e3715
      have b0e3734 : False := by grind
      exact b0e3734
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
        have b1e45 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e52 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e45
             have r₂ := b1e21
             grind)
          | exact resolve b1e45 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e53 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e54 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e53
          | exact resolve b1e53 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e53
        have b1e55 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e19
          | exact resolve b1e19 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e22
          | exact resolve b1e22 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e59 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e13
          | exact resolve b1e13 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : x = y := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e59
          | exact resolve b1e59 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e63 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e55
          | exact resolve b1e55 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e56
        have b1e64 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e63
          | exact resolve b1e63 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e63
        have b1e65 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e64
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e64
          | exact resolve b1e64 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e66 : False := by grind
        exact b1e66
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b2e25 : y = (k x y) := by grind
        have b2e28 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 y))) = X0 := by
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
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
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
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : y = (M.op y (M.op x x)) := by
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
        have b2e36 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          grind
        have b2e37 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b2e56 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
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
        have b2e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ x)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ x) (σ x)) x
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e133 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e29 X0 X0 x x
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e140 : y = (M.op y x) := by
          first
          | (have i₁ := b2e133 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e133
          | exact resolve b2e133 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e175 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e31 X0 (M.op X0 X1) X0 X1
             have i₂ := b2e133 (M.op X0 X1)
             grind)
          | exact superpose b2e133 b2e31
          | exact resolve b2e31 b2e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e133
        have b2e188 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e140
             grind)
          | exact superpose b2e140 b2e12
          | exact resolve b2e12 b2e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e140
        have b2e195 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e197 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e195 X0
             have j1 := b2e36 X0
             grind)
          | (have r₁ := b2e195 X0
             have r₂ := b2e36 X0
             grind)
          | exact resolve b2e195 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e195
        have b2e198 : y = (k y x) := by
          first
          | (have i₁ := b2e197 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e197
          | exact resolve b2e197 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e197
        have b2e496 : x = (M.op x y) := by
          first
          | (have i₁ := b2e188 x
             have i₂ := b2e32
             grind)
          | exact superpose b2e32 b2e188
          | exact resolve b2e188 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e188
        have b2e506 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e56 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e507 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e506
             have r₂ := b2e22
             grind)
          | exact resolve b2e506 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e506
        have b2e508 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e507
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e507
          | exact resolve b2e507 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e507
        have b2e509 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e508
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e508
          | exact resolve b2e508 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e508
        have b2e520 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have j0 := b2e57 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e521 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b2e520
             have r₂ := b2e21
             grind)
          | exact resolve b2e520 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e520
        have b2e522 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e521
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e521
          | exact resolve b2e521 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e521
        have b2e523 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e522
             have i₂ := b2e198
             grind)
          | exact superpose b2e198 b2e522
          | exact resolve b2e522 b2e198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e198 b2e522
        have b2e535 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e523
             grind)
          | exact superpose b2e523 b2e19
          | exact resolve b2e19 b2e523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e542 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b2e175 (σ x) (σ y)
             have i₂ := b2e523
             grind)
          | exact superpose b2e523 b2e175
          | exact resolve b2e175 b2e523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175
        have b2e543 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e542
             have i₂ := b2e509
             grind)
          | exact superpose b2e509 b2e542
          | exact resolve b2e542 b2e509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e509 b2e542
        have b2e544 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e535
             have i₂ := b2e496
             grind)
          | exact superpose b2e496 b2e535
          | exact resolve b2e535 b2e496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e496 b2e535
        have b2e545 : (σ x) = (σ y) := by
          first
          | (have i₁ := b2e543
             have i₂ := b2e523
             grind)
          | exact superpose b2e523 b2e543
          | exact resolve b2e543 b2e523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e523 b2e543
        have b2e546 : False := by grind
        exact b2e546
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
        have b3e32 : (k x y) = (τ (σ y)) := by
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
        have b3e33 : y = (k x y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e32
          | exact resolve b3e32 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e46 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e51 : x = (k x y) := by
          first
          | (have r₁ := b3e46
             have r₂ := b3e20
             grind)
          | exact resolve b3e46 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e53 : x = y := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e51
          | exact resolve b3e51 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e51
        have b3e55 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e19
          | exact resolve b3e19 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e21
          | exact resolve b3e21 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e61 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e55
          | exact resolve b3e55 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e56
        have b3e62 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e61
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e61
          | exact resolve b3e61 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e63 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e62
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e62
          | exact resolve b3e62 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e62
        have b3e64 : False := by grind
        exact b3e64
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e38 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e194 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e38 X0 X0 x x
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e204 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e194 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e194
            | exact resolve b4e194 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e205 : x = (M.op x y) := by
            first
            | (have i₁ := b4e194 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e194
            | exact resolve b4e194 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194
          have b4e324 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e204
               grind)
            | exact superpose b4e204 b4e20
            | exact resolve b4e20 b4e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204
          have b4e331 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e324
               have i₂ := b4e205
               grind)
            | exact superpose b4e205 b4e324
            | exact resolve b4e324 b4e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e205 b4e324
          have b4e332 : False := by grind
          exact b4e332
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
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
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
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
          have b5e132 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e35 X0 X0 x x
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e139 : x = (M.op x y) := by
            first
            | (have i₁ := b5e132 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e132
            | exact resolve b5e132 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e517 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e518 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e517
               have r₂ := b5e23
               grind)
            | exact resolve b5e517 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e517
          have b5e519 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e518
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e518
            | exact resolve b5e518 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e518
          have b5e520 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e519
               have i₂ := b5e27
               grind)
            | exact superpose b5e27 b5e519
            | exact resolve b5e519 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e519
          have b5e521 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e520
               grind)
            | exact superpose b5e520 b5e20
            | exact resolve b5e20 b5e520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e520
          have b5e529 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e521
               have i₂ := b5e139
               grind)
            | exact superpose b5e139 b5e521
            | exact resolve b5e521 b5e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e139 b5e521
          have b5e530 : False := by grind
          exact b5e530
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b6e27 : (k x y) = (τ (σ y)) := by
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
        have b6e28 : y = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e40 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
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
        have b6e42 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
             have i₂ := b6e12 X0 X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          grind
        have b6e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b6e99 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
        have b6e104 : y = (M.op y x) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e99
             have r₂ := b6e20
             grind)
          | exact resolve b6e99 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e107 : y = (M.op y x) := by
          first
          | (have r₁ := b6e104
             have r₂ := b6e21
             grind)
          | exact resolve b6e104 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e166 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e40 X0 X0 x x
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e40
          | exact resolve b6e40 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e212 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e42 X0 (M.op X0 X1) X0 X1
             have i₂ := b6e166 (M.op X0 X1)
             grind)
          | exact superpose b6e166 b6e42
          | exact resolve b6e42 b6e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e166
        have b6e273 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e55 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e275 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e273 X0
             have j1 := b6e54 X0
             grind)
          | (have r₁ := b6e273 X0
             have r₂ := b6e54 X0
             grind)
          | exact resolve b6e273 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e273
        have b6e282 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e275 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e275
          | exact resolve b6e275 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e275
        have b6e288 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e282
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e282
          | exact resolve b6e282 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e282
        have b6e336 : (τ (σ y)) = (k y x) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e288
             grind)
          | exact superpose b6e288 b6e13
          | exact resolve b6e13 b6e288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e288
        have b6e337 : y = (k y x) := by
          first
          | (have i₁ := b6e336
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e336
          | exact resolve b6e336 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e336
        have b6e410 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e337
             grind)
          | exact superpose b6e337 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e337
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e337
        have b6e411 : y = (M.op x y) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e410
             have r₂ := b6e21
             grind)
          | exact resolve b6e410 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e410
        have b6e415 : y = (M.op x y) := by
          first
          | (have r₁ := b6e411
             have r₂ := b6e20
             grind)
          | exact resolve b6e411 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e411
        have b6e473 : x = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b6e212 x y
             have i₂ := b6e415
             grind)
          | exact superpose b6e415 b6e212
          | exact resolve b6e212 b6e415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e212
        have b6e474 : x = (M.op x y) := by
          first
          | (have i₁ := b6e473
             have i₂ := b6e107
             grind)
          | exact superpose b6e107 b6e473
          | exact resolve b6e473 b6e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e107 b6e473
        have b6e475 : x = y := by
          first
          | (have i₁ := b6e474
             have i₂ := b6e415
             grind)
          | exact superpose b6e415 b6e474
          | exact resolve b6e474 b6e415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e474
        have b6e563 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e475
             grind)
          | exact superpose b6e475 b6e21
          | exact resolve b6e21 b6e475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e575 : y = (M.op y y) := by
          first
          | (have i₁ := b6e415
             have i₂ := b6e475
             grind)
          | exact superpose b6e475 b6e415
          | exact resolve b6e415 b6e475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e415 b6e475
        have b6e576 : False := by grind
        exact b6e576
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e88 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e28
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e28 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e91 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e88
               have r₂ := b7e22
               grind)
            | exact resolve b7e88 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e95 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e91
               have r₂ := b7e21
               grind)
            | exact resolve b7e91 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e172 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e38 X0 X0 x x
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e38
            | exact resolve b7e38 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e182 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e172 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e172
            | exact resolve b7e172 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e172
          have b7e224 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e182
               grind)
            | exact superpose b7e182 b7e20
            | exact resolve b7e20 b7e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e182
          have b7e231 : False := by grind
          exact b7e231
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
          have b8e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
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
          have b8e590 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e591 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e590
               have r₂ := b8e23
               grind)
            | exact resolve b8e590 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e590
          have b8e592 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e591
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e591
            | exact resolve b8e591 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e591
          have b8e593 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e592
               grind)
            | exact superpose b8e592 b8e20
            | exact resolve b8e20 b8e592
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e592
          have b8e604 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e593
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e593
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e593 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e593
          have b8e615 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e604
          have b8e622 : x = (M.op y y) := by
            first
            | (have r₁ := b8e615
               have r₂ := b8e22
               grind)
            | exact resolve b8e615 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e615
          have b8e625 : False := by grind
          exact b8e625

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation854 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
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
      have b0e59 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e62 : False := by grind
      exact b0e62
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 := by
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
          have b4e33 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ x)))) = X0 := by
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
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : y = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b4e32 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e66 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          have b4e70 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e66 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e66
            | exact resolve b4e66 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e71
          have b4e80 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e27 X1 X0
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e88 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
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
          have b4e90 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b4e33 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e33
            | exact resolve b4e33 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e96 : (σ y) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b4e90
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e90
            | exact resolve b4e90 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e97 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e70 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e70
            | exact resolve b4e70 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e129 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op y (M.op X1 (M.op y y)))))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X1 X0 y (M.op y y)
               have i₂ := b4e38
               grind)
            | exact superpose b4e38 b4e34
            | exact resolve b4e34 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e148 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 X0 X0 x x
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e154 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e148 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e148
            | exact resolve b4e148 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e160 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op X0 X0)
               have i₂ := b4e148 X0
               grind)
            | exact superpose b4e148 b4e13
            | exact resolve b4e13 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148
          have b4e226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b4e240 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e226
               have r₂ := b4e23
               grind)
            | exact resolve b4e226 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226
          have b4e254 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e80 X1 X0
               have i₂ := b4e18 (σ X1) X0
               grind)
            | exact superpose b4e18 b4e80
            | (have j1 := b4e18 (σ X1) X0
               grind)
            | exact resolve b4e80 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e303 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ (M.op y y))))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ (M.op y y))
               have i₂ := b4e96
               grind)
            | exact superpose b4e96 b4e13
            | exact resolve b4e13 b4e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e424 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ X0) X1 (σ (M.op X0 X0))
               have i₂ := b4e154 X0
               grind)
            | exact superpose b4e154 b4e13
            | exact resolve b4e13 b4e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154
          have b4e629 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e160 X0 (M.op X1 X0)
               have i₂ := b4e13 X0 X1 X0
               grind)
            | exact superpose b4e13 b4e160
            | exact resolve b4e160 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e712 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X0 X1) X2 X1
               have i₂ := b4e629 X1 X0
               grind)
            | exact superpose b4e629 b4e13
            | exact resolve b4e13 b4e629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e713 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 (M.op X0 X1)
               have i₂ := b4e629 X1 X0
               grind)
            | exact superpose b4e629 b4e17
            | (have j0 := b4e17 (M.op X0 X1) X1
               grind)
            | (have r₁ := b4e17 X0 (M.op X1 X0)
               have r₂ := b4e629 X0 X1
               grind)
            | exact resolve b4e17 b4e629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e741 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e713 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e713
          have b4e793 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (σ (M.op X0 X0)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e88 X0 (σ X1)
               have i₂ := b4e54 X1 X0
               grind)
            | exact superpose b4e54 b4e88
            | (have j1 := b4e54 X1 X0
               grind)
            | exact resolve b4e88 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54 b4e88
          have b4e962 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (τ X0)))) ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X0 (M.op X1 (τ X0))
               have i₂ := b4e741 X1 (τ X0)
               grind)
            | exact superpose b4e741 b4e26
            | (have j1 := b4e741 X1 (τ X0)
               grind)
            | exact resolve b4e26 b4e741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e965 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ X0)))) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e962 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e962
            | (have j0 := b4e962 X0 X1
               grind)
            | exact resolve b4e962 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e962
          have b4e1861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e240
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e240
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e240
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e240
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e240 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e240
          have b4e1862 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e1861
          have b4e1863 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1862
               have r₂ := b4e21
               grind)
            | exact resolve b4e1862 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1862
          have b4e1884 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e741 (σ x) (σ y)
               have i₂ := b4e1863
               grind)
            | exact superpose b4e1863 b4e741
            | exact resolve b4e741 b4e1863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e741 b4e1863
          have b4e1886 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1884
               have r₂ := b4e23
               grind)
            | exact resolve b4e1884 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1884
          have b4e1889 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1886
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e1886
            | exact resolve b4e1886 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1886
          have b4e1971 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e1889
               grind)
            | exact superpose b4e1889 b4e14
            | exact resolve b4e14 b4e1889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1889
          have b4e2011 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1971
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e1971
            | exact resolve b4e1971 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1971
          have b4e11829 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ (M.op X1 X0))) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e965 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e965
            | exact resolve b4e965 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e965
          have b4e11917 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X0))) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e11829 X0 X1
               have i₂ := b4e19 X0 (M.op X1 X0)
               grind)
            | exact superpose b4e19 b4e11829
            | (have j0 := b4e11829 X0 X1
               grind)
            | exact resolve b4e11829 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11829
          have b4e17960 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e254 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e254
            | exact resolve b4e254 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e254
          have b4e18017 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e17960 X0 X1
               have i₂ := b4e97 X1 X0
               grind)
            | exact superpose b4e97 b4e17960
            | (have j0 := b4e17960 X0 X1
               grind)
            | exact resolve b4e17960 b4e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97 b4e17960
          have b4e34565 : (τ y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e18017 y x
               have i₂ := b4e2011
               grind)
            | exact superpose b4e2011 b4e18017
            | (have j0 := b4e18017 y x
               grind)
            | exact resolve b4e18017 b4e2011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2011 b4e18017
          have b4e34675 : (τ y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e34565
          have b4e34736 : (τ y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e34675
               have r₂ := b4e21
               grind)
            | exact resolve b4e34675 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34675
          have b4e34851 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (τ y) (τ y))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e72 (M.op x y)
               have i₂ := b4e34736
               grind)
            | exact superpose b4e34736 b4e72
            | exact resolve b4e72 b4e34736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34736
          have b4e34938 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e34851
               have i₂ := b4e72 y
               grind)
            | exact superpose b4e72 b4e34851
            | exact resolve b4e34851 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e34851
          have b4e35043 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e13 x x y
               have i₂ := b4e34938
               grind)
            | exact superpose b4e34938 b4e13
            | exact resolve b4e13 b4e34938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34938
          have b4e35307 : x = (M.op x (M.op y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e160 y x
               have i₂ := b4e35043
               grind)
            | exact superpose b4e35043 b4e160
            | exact resolve b4e160 b4e35043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160 b4e35043
          have b4e35372 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e35307
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35307
            | exact resolve b4e35307 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35307
          have b4e35373 : x = (M.op x y) := by grind
          clear b4e35372
          have b4e35543 : (σ y) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b4e11917 y x
               have i₂ := b4e35373
               grind)
            | exact superpose b4e35373 b4e11917
            | exact resolve b4e11917 b4e35373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11917
          have b4e35547 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b4e35543
               have r₂ := b4e21
               grind)
            | exact resolve b4e35543 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35543
          have b4e100861 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e793 y x
               have i₂ := b4e35547
               grind)
            | exact superpose b4e35547 b4e793
            | (have j0 := b4e793 y x
               grind)
            | exact resolve b4e793 b4e35547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e793 b4e35547
          have b4e100973 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e100861
               have r₂ := b4e23
               grind)
            | exact resolve b4e100861 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100861
          have b4e100984 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e100973
               have i₂ := b4e96
               grind)
            | exact superpose b4e96 b4e100973
            | exact resolve b4e100973 b4e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96 b4e100973
          have b4e100994 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e100984
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e100984
            | exact resolve b4e100984 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e100984
          have b4e101009 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e100994
               grind)
            | exact superpose b4e100994 b4e20
            | exact resolve b4e20 b4e100994
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100994
          have b4e101128 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e101009
               have i₂ := b4e35373
               grind)
            | exact superpose b4e35373 b4e101009
            | exact resolve b4e101009 b4e35373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35373 b4e101009
          have b4e101129 : (σ y) = (σ (M.op y y)) := by grind
          clear b4e101128
          have b4e101304 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e424 y X0
               have i₂ := b4e101129
               grind)
            | exact superpose b4e101129 b4e424
            | exact resolve b4e424 b4e101129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e424
          have b4e101345 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e101129
               grind)
            | exact superpose b4e101129 b4e14
            | exact resolve b4e14 b4e101129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101502 : y = (M.op y y) := by
            first
            | (have i₁ := b4e101345
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e101345
            | exact resolve b4e101345 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101345
          have b4e101521 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e101304 X0
               have i₂ := b4e629 (σ y) X0
               grind)
            | exact superpose b4e629 b4e101304
            | exact resolve b4e101304 b4e629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101304
          have b4e101833 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e101502
               grind)
            | exact superpose b4e101502 b4e13
            | exact resolve b4e13 b4e101502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101876 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b4e712 y y x
               have i₂ := b4e101502
               grind)
            | exact superpose b4e101502 b4e712
            | exact resolve b4e712 b4e101502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101502
          have b4e101936 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e101876 X0
               have i₂ := b4e629 y X0
               grind)
            | exact superpose b4e629 b4e101876
            | exact resolve b4e101876 b4e629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e629 b4e101876
          have b4e102661 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e101833 X0
               have i₂ := b4e101936 X0
               grind)
            | exact superpose b4e101936 b4e101833
            | exact resolve b4e101833 b4e101936
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e102749 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op X0 y))) = (M.op (M.op X1 (M.op y (M.op X0 y))) (M.op X0 (M.op X1 (M.op y (M.op X0 y))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e712 X1 (M.op y (M.op X0 y)) X0
               have i₂ := b4e101833 X0
               grind)
            | exact superpose b4e101833 b4e712
            | exact resolve b4e712 b4e101833
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e712 b4e101833
          have b4e102857 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 y) (M.op X0 (M.op X1 y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e102749 X0 X1
               have i₂ := b4e101936 X0
               grind)
            | exact superpose b4e101936 b4e102749
            | exact resolve b4e102749 b4e101936
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101936 b4e102749
          have b4e102927 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e102857 X0 X0
               have i₂ := b4e102661 X0
               grind)
            | exact superpose b4e102661 b4e102857
            | exact resolve b4e102857 b4e102661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102857
          have b4e105798 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ (M.op y y)))) = (M.op (M.op (σ y) (M.op X0 (σ (M.op y y)))) X0) := by
            intro X0
            first
            | (have i₁ := b4e102927 X0 (M.op (σ y) (M.op X0 (σ (M.op y y))))
               have i₂ := b4e303 X0
               grind)
            | exact superpose b4e303 b4e102927
            | exact resolve b4e102927 b4e303
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e303 b4e102927
          have b4e106705 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ y) (M.op X0 (σ y))) X0) := by
            intro X0
            first
            | (have i₁ := b4e105798 X0
               have i₂ := b4e101129
               grind)
            | exact superpose b4e101129 b4e105798
            | exact resolve b4e105798 b4e101129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101129 b4e105798
          have b4e106723 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e106705 X0
               have i₂ := b4e101521 X0
               grind)
            | exact superpose b4e101521 b4e106705
            | exact resolve b4e106705 b4e101521
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101521 b4e106705
          have b4e109550 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e129 X0 (σ y)
               have i₂ := b4e106723 (M.op X0 (M.op y (M.op (σ y) (M.op y y))))
               grind)
            | exact superpose b4e106723 b4e129
            | exact resolve b4e129 b4e106723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129 b4e106723
          have b4e110870 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e109550 (σ x)
               grind)
            | exact superpose b4e109550 b4e20
            | exact resolve b4e20 b4e109550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109550
          have b4e110875 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e110870
               have i₂ := b4e102661 x
               grind)
            | exact superpose b4e102661 b4e110870
            | exact resolve b4e110870 b4e102661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102661 b4e110870
          have b4e110876 : False := by grind
          exact b4e110876
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e44 : x = y ∨ x = (k x y) := by grind
          clear b5e39
          have b5e45 : x = (k x y) := by
            first
            | (have r₁ := b5e44
               have r₂ := b5e21
               grind)
            | exact resolve b5e44 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e98 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 X0 X0 x x
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e110 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X0 X0)
               have i₂ := b5e98 X0
               grind)
            | exact superpose b5e98 b5e13
            | exact resolve b5e13 b5e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e166 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (σ X1) (σ X0)
               have i₂ := b5e48 X1 X0
               grind)
            | exact superpose b5e48 b5e13
            | (have j1 := b5e48 X1 X0
               grind)
            | exact resolve b5e13 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e565 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e110 X0 (M.op X1 X0)
               have i₂ := b5e13 X0 X1 X0
               grind)
            | exact superpose b5e13 b5e110
            | exact resolve b5e110 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5145 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e166 x y X0
               have i₂ := b5e45
               grind)
            | exact superpose b5e45 b5e166
            | (have j0 := b5e166 x y x
               grind)
            | exact resolve b5e166 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45 b5e166
          have b5e5220 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e5145 X0
               grind)
            | (have r₁ := b5e5145 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e5145 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5145
          have b5e5224 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 := by
            intro X0
            first
            | (have j0 := b5e5220 X0
               grind)
            | (have r₁ := b5e5220 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e5220 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5220
          have b5e5256 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e110 (σ x) (σ x)
               have i₂ := b5e5224 (σ x)
               grind)
            | exact superpose b5e5224 b5e110
            | exact resolve b5e110 b5e5224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e110
          have b5e5301 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e5256
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e5256
            | exact resolve b5e5256 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e5256
          have b5e5440 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 (M.op x x)
               have i₂ := b5e5301
               grind)
            | exact superpose b5e5301 b5e14
            | exact resolve b5e14 b5e5301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5301
          have b5e5484 : x = (M.op x x) := by
            first
            | (have i₁ := b5e5440
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e5440
            | exact resolve b5e5440 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5440
          have b5e5640 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e5484
               grind)
            | exact superpose b5e5484 b5e13
            | exact resolve b5e13 b5e5484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5641 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 x
               have i₂ := b5e5484
               grind)
            | exact superpose b5e5484 b5e13
            | exact resolve b5e13 b5e5484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5484
          have b5e5694 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e5641 X0
               have i₂ := b5e565 x X0
               grind)
            | exact superpose b5e565 b5e5641
            | exact resolve b5e5641 b5e565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e565 b5e5641
          have b5e6404 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e5640 X0
               have i₂ := b5e5694 X0
               grind)
            | exact superpose b5e5694 b5e5640
            | exact resolve b5e5640 b5e5694
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5640 b5e5694
          have b5e6627 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 x) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e6404 X0
               grind)
            | exact superpose b5e6404 b5e13
            | exact resolve b5e13 b5e6404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e6736 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e6627 X0 X1
               have i₂ := b5e6404 X1
               grind)
            | exact superpose b5e6404 b5e6627
            | exact resolve b5e6627 b5e6404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6404 b5e6627
          have b5e8454 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e5224 X0
               have i₂ := b5e6736 (σ x) X0
               grind)
            | exact superpose b5e6736 b5e5224
            | exact resolve b5e5224 b5e6736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5224 b5e6736
          have b5e8721 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e8454 (σ y)
               grind)
            | exact superpose b5e8454 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e8454 (σ y)
               grind)
            | exact resolve b5e24 b5e8454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8454
          have b5e8725 : False := by grind
          exact b5e8725
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          clear b7e43
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
          have b7e62 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
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
          have b7e63 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e65 : x = (M.op y x) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e81 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e13
            | exact resolve b7e13 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y x
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e13
            | exact resolve b7e13 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e105 : y = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b7e81 y
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e81
            | exact resolve b7e81 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e81
          have b7e139 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0 X0 x x
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e33
            | exact resolve b7e33 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e281 : x = (M.op x x) := by
            first
            | (have i₁ := b7e82 x
               have i₂ := b7e139 x
               grind)
            | exact superpose b7e139 b7e82
            | exact resolve b7e82 b7e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e139
          have b7e313 : y = (M.op y x) := by
            first
            | (have i₁ := b7e105
               have i₂ := b7e281
               grind)
            | exact superpose b7e281 b7e105
            | exact resolve b7e105 b7e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105 b7e281
          have b7e326 : False := by grind
          exact b7e326
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          have b8e38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e26 X0 X1
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e39 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e35 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e35
            | exact resolve b8e35 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35
          have b8e40 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e39
          have b8e41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X2) (M.op X0 X2)) = X0 ∨ (M.op (M.op X1 X2) (M.op X0 X2)) = (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 (M.op (M.op X1 X2) (M.op X0 X2)) X0
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e17
            | (have j0 := b8e17 (M.op (M.op X1 X2) (M.op X0 X2)) X0
               grind)
            | (have r₁ := b8e17 (M.op (M.op X1 X2) (M.op X0 X2)) X0
               have r₂ := b8e13 X0 X1 X2
               grind)
            | exact resolve b8e17 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X2)) = (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) ∨ (M.op (M.op X1 X2) (M.op X0 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e41 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41
          have b8e49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e69 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 X0 X0 x x
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e80 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 (M.op X0 X0)
               have i₂ := b8e69 X0
               grind)
            | exact superpose b8e69 b8e13
            | exact resolve b8e13 b8e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e81 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0 (M.op X0 X0)
               have i₂ := b8e69 X0
               grind)
            | exact superpose b8e69 b8e13
            | exact resolve b8e13 b8e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e124 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e125 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 (σ X1) (σ X0)
               have i₂ := b8e56 X1 X0
               grind)
            | exact superpose b8e56 b8e13
            | (have j1 := b8e56 X1 X0
               grind)
            | exact resolve b8e13 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e136 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e124
               have r₂ := b8e23
               grind)
            | exact resolve b8e124 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e140 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e38
            | exact resolve b8e38 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e154 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))))) = (k (M.op X0 (M.op X4 (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))))) X4) ∨ (M.op X0 (M.op X4 (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3)))))) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e42 X0 X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))
               have i₂ := b8e32 X0 X1 X2 X3
               grind)
            | exact superpose b8e32 b8e42
            | exact resolve b8e42 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e42
          have b8e188 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e49 X1 X0
               have i₂ := b8e18 (σ X1) X0
               grind)
            | exact superpose b8e18 b8e49
            | (have j1 := b8e18 (σ X1) X0
               grind)
            | exact resolve b8e49 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e451 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e81 X0 (M.op X1 X0)
               have i₂ := b8e13 X0 X1 X0
               grind)
            | exact superpose b8e13 b8e81
            | exact resolve b8e81 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e513 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X0 X1) X2 X1
               have i₂ := b8e451 X1 X0
               grind)
            | exact superpose b8e451 b8e13
            | exact resolve b8e13 b8e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e514 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 (M.op X0 X1)
               have i₂ := b8e451 X1 X0
               grind)
            | exact superpose b8e451 b8e17
            | (have j0 := b8e17 (M.op X0 X1) X1
               grind)
            | (have r₁ := b8e17 X0 (M.op X1 X0)
               have r₂ := b8e451 X0 X1
               grind)
            | exact resolve b8e17 b8e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e451
          have b8e528 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e514 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e514
          have b8e656 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e136
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e136
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e136
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e136
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e136 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e657 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e656
          have b8e658 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e657
               have r₂ := b8e21
               grind)
            | exact resolve b8e657 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e657
          have b8e879 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e528 (σ x) (σ y)
               have i₂ := b8e658
               grind)
            | exact superpose b8e658 b8e528
            | exact resolve b8e528 b8e658
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e528 b8e658
          have b8e881 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e879
               have r₂ := b8e23
               grind)
            | exact resolve b8e879 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e879
          have b8e884 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e881
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e881
            | exact resolve b8e881 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e881
          have b8e1072 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e884
               grind)
            | exact superpose b8e884 b8e14
            | exact resolve b8e14 b8e884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1080 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (k X0 (σ y))) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e38 X0 (k y x)
               have i₂ := b8e884
               grind)
            | exact superpose b8e884 b8e38
            | exact resolve b8e38 b8e884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1085 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (σ y) X0)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e49 (k y x) X0
               have i₂ := b8e884
               grind)
            | exact superpose b8e884 b8e49
            | exact resolve b8e49 b8e884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e884
          have b8e1096 : ∀ X0 : G, (k (k y x) (τ X0)) = (k y (τ X0)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e1085 X0
               have i₂ := b8e49 y X0
               grind)
            | exact superpose b8e49 b8e1085
            | exact resolve b8e1085 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e1085
          have b8e1101 : ∀ X0 : G, (k (τ X0) (k y x)) = (k (τ X0) y) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e1080 X0
               have i₂ := b8e38 X0 y
               grind)
            | exact superpose b8e38 b8e1080
            | exact resolve b8e1080 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e1080
          have b8e1109 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1072
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e1072
            | exact resolve b8e1072 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1072
          have b8e3535 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 (σ (τ X0))))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e125 (τ X0) (τ X1) X2
               have i₂ := b8e140 X1 X0
               grind)
            | exact superpose b8e140 b8e125
            | (have j0 := b8e125 (τ X0) (τ X1) X2
               grind)
            | exact resolve b8e125 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3543 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (k (τ X0) X2)) (M.op X1 X0))) = X1 ∨ (σ X2) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e125 (τ X0) X1 X2
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e125
            | exact resolve b8e125 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3605 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X0 (σ X2)) (M.op X1 X0))) = X1 ∨ (σ X2) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3543 X0 X1 X2
               have i₂ := b8e26 X0 X2
               grind)
            | exact superpose b8e26 b8e3543
            | (have j0 := b8e3543 X0 X1 X2
               grind)
            | exact resolve b8e3543 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e3543
          have b8e3609 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ (k X0 X1))) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3535 X0 X1 X2
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e3535
            | (have j0 := b8e3535 X0 X1 X2
               grind)
            | exact resolve b8e3535 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3535
          have b8e3612 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3609 X0 X1 X2
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e3609
            | (have j0 := b8e3609 X0 X1 X2
               grind)
            | exact resolve b8e3609 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3609
          have b8e3614 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3612 X0 X1 X2
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e3612
            | (have j0 := b8e3612 X0 X1 X2
               grind)
            | exact resolve b8e3612 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3612
          have b8e3615 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3614 X0 X0 X2
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e3614
            | (have j0 := b8e3614 X0 X1 X2
               grind)
            | exact resolve b8e3614 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3614
          have b8e3616 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3615 X0 X1 X2
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e3615
            | (have j0 := b8e3615 X0 X1 X2
               grind)
            | exact resolve b8e3615 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3615
          have b8e3617 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (k X0 X1) (M.op X2 X0))) = X2 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3616 X0 X1 X2
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e3616
            | (have j0 := b8e3616 X0 X1 X2
               grind)
            | exact resolve b8e3616 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3616
          have b8e10701 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e188 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e188
            | exact resolve b8e188 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188
          have b8e10763 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e10701 X0 X1
               have i₂ := b8e140 X1 X0
               grind)
            | exact superpose b8e140 b8e10701
            | (have j0 := b8e10701 X0 X1
               grind)
            | exact resolve b8e10701 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140 b8e10701
          have b8e16575 : ∀ X0 : G, (k (k y x) X0) = (k y X0) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e1096 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e1096
            | exact resolve b8e1096 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1096
          have b8e17329 : ∀ X0 : G, (k X0 (k y x)) = (k X0 y) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e1101 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e1101
            | exact resolve b8e1101 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1101
          have b8e17590 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e17329 X0
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e17329
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e17329 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e17659 : (k y (k y x)) = (k (k y x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16575 (k y x)
               have i₂ := b8e17329 (k y x)
               grind)
            | exact superpose b8e17329 b8e16575
            | exact resolve b8e16575 b8e17329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17329
          have b8e17666 : (k y (k y x)) = (k (k y x) y) ∨ x = (M.op x y) := by grind
          clear b8e17659
          have b8e17670 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e17590 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17590
          have b8e17693 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e17670 X0
               grind)
            | (have r₁ := b8e17670 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e17670 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17670
          have b8e17941 : (k y (M.op x y)) = (k (k y x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16575 (M.op x y)
               have i₂ := b8e17693 (k y x)
               grind)
            | exact superpose b8e17693 b8e16575
            | exact resolve b8e16575 b8e17693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16575 b8e17693
          have b8e17948 : (k y (M.op x y)) = (k (k y x) y) ∨ x = (M.op x y) := by grind
          clear b8e17941
          have b8e18776 : ∀ X0 X1 X2 X3 : G, (k X0 (k (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) (σ X3))) = X0 ∨ (k (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) (σ X3)) = X0 ∨ (σ X3) = (M.op (σ X3) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) ∨ (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = (σ X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e154 X1 X1 X2 X3 (k (M.op X1 (M.op (M.op X2 X3) (M.op X1 X3))) (σ X2))
               have i₂ := b8e3605 (M.op X1 (M.op (M.op X2 X3) (M.op X1 X3))) X1 X2
               grind)
            | exact superpose b8e3605 b8e154
            | (have j1 := b8e3605 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) X1 X3
               grind)
            | exact resolve b8e154 b8e3605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154 b8e3605
          have b8e18901 : ∀ X0 X1 X2 X3 : G, (k X0 (k X0 (σ X3))) = X0 ∨ (k (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) (σ X3)) = X0 ∨ (σ X3) = (M.op (σ X3) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) ∨ (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = (σ X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e18776 X0 X1 X2 X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e18776
            | (have j0 := b8e18776 X0 X1 X2 X3
               grind)
            | exact resolve b8e18776 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18776
          have b8e18941 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X3)) = X0 ∨ (k X0 (k X0 (σ X3))) = X0 ∨ (σ X3) = (M.op (σ X3) (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2)))) ∨ (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = (σ X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e18901 X0 X1 X2 X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e18901
            | (have j0 := b8e18901 X0 X1 X2 X3
               grind)
            | exact resolve b8e18901 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18901
          have b8e18967 : ∀ X0 X1 X2 X3 : G, (σ X3) = (M.op (σ X3) X0) ∨ (k X0 (σ X3)) = X0 ∨ (k X0 (k X0 (σ X3))) = X0 ∨ (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = (σ X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e18941 X0 X1 X2 X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e18941
            | (have j0 := b8e18941 X0 X1 X2 X3
               grind)
            | exact resolve b8e18941 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18941
          have b8e18979 : ∀ X0 X3 : G, (σ X3) = X0 ∨ (σ X3) = (M.op (σ X3) X0) ∨ (k X0 (σ X3)) = X0 ∨ (k X0 (k X0 (σ X3))) = X0 := by
            intro X0 X3
            first
            | (have i₁ := b8e18967 X0 x x X3
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e18967
            | (have j0 := b8e18967 X0 x x X3
               grind)
            | exact resolve b8e18967 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18967
          have b8e18983 : ∀ X0 X3 : G, (k X0 (k X0 (σ X3))) = X0 ∨ (k X0 (σ X3)) = X0 ∨ (σ X3) = X0 := by
            intro X0 X3
            first
            | (have j0 := b8e18979 X0 X3
               have j1 := b8e17 (k X0 (k X0 (σ X3))) X0
               grind)
            | (have r₁ := b8e18979 (M.op (σ X3) X0) X3
               have r₂ := b8e17 X0 (σ X3)
               grind)
            | (have r₁ := b8e18979 X0 X3
               have r₂ := b8e17 X0 (σ X3)
               grind)
            | exact resolve b8e18979 b8e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18979
          have b8e30069 : (k y (M.op x y)) = (k y (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17666
               have i₂ := b8e17948
               grind)
            | exact superpose b8e17948 b8e17666
            | exact resolve b8e17666 b8e17948
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17666 b8e17948
          have b8e30092 : (k y (M.op x y)) = (k y (k y x)) ∨ x = (M.op x y) := by grind
          clear b8e30069
          have b8e44418 : (τ y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e10763 y x
               have i₂ := b8e1109
               grind)
            | exact superpose b8e1109 b8e10763
            | (have j0 := b8e10763 y x
               grind)
            | exact resolve b8e10763 b8e1109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10763
          have b8e44553 : (τ y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e44418
          have b8e44607 : (τ y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e44553
               have r₂ := b8e21
               grind)
            | exact resolve b8e44553 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44553
          have b8e45057 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (τ y) (τ y))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e40 (M.op x y)
               have i₂ := b8e44607
               grind)
            | exact superpose b8e44607 b8e40
            | exact resolve b8e40 b8e44607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44607
          have b8e45167 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e45057
               have i₂ := b8e40 y
               grind)
            | exact superpose b8e40 b8e45057
            | exact resolve b8e45057 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e45057
          have b8e45189 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e13 x x y
               have i₂ := b8e45167
               grind)
            | exact superpose b8e45167 b8e13
            | exact resolve b8e13 b8e45167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45167
          have b8e45673 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e80 y x
               have i₂ := b8e45189
               grind)
            | exact superpose b8e45189 b8e80
            | exact resolve b8e80 b8e45189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80 b8e45189
          have b8e60448 : ∀ X0 X1 : G, (k X1 (k X1 X0)) = X1 ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e18983 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e18983
            | exact resolve b8e18983 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18983
          have b8e61805 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e30092
               have i₂ := b8e60448 x y
               grind)
            | exact superpose b8e60448 b8e30092
            | (have j1 := b8e60448 x y
               grind)
            | exact resolve b8e30092 b8e60448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30092 b8e60448
          have b8e61831 : y = (k y (M.op x y)) ∨ y = (k y x) ∨ x = y := by
            first
            | (have j1 := b8e17 y (k y (M.op x y))
               grind)
            | (have r₁ := b8e61805
               have r₂ := b8e17 y x
               grind)
            | exact resolve b8e61805 b8e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61805
          have b8e61925 : y = (k y (M.op x y)) ∨ y = (k y x) := by
            first
            | (have r₁ := b8e61831
               have r₂ := b8e21
               grind)
            | exact resolve b8e61831 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61831
          have b8e188509 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e3617 y x X0
               have i₂ := b8e1109
               grind)
            | exact superpose b8e1109 b8e3617
            | (have j0 := b8e3617 y x x
               grind)
            | exact resolve b8e3617 b8e1109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1109 b8e3617
          have b8e188539 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e188509 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188509
          have b8e188541 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e188539 X0
               grind)
            | (have r₁ := b8e188539 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e188539 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188539
          have b8e191495 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e188541 x
               have i₂ := b8e45673
               grind)
            | exact superpose b8e45673 b8e188541
            | exact resolve b8e188541 b8e45673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45673 b8e188541
          have b8e191552 : x = (M.op x y) := by grind
          clear b8e191495
          have b8e191954 : y = (k y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e61925
               have i₂ := b8e191552
               grind)
            | exact superpose b8e191552 b8e61925
            | exact resolve b8e61925 b8e191552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61925
          have b8e192007 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) (M.op x (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b8e513 X0 y x
               have i₂ := b8e191552
               grind)
            | exact superpose b8e191552 b8e513
            | exact resolve b8e513 b8e191552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e513
          have b8e192073 : y = (k y x) := by grind
          clear b8e191954
          have b8e192535 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e125 y x X0
               have i₂ := b8e192073
               grind)
            | exact superpose b8e192073 b8e125
            | (have j0 := b8e125 y x x
               grind)
            | exact resolve b8e125 b8e192073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e125 b8e192073
          have b8e192542 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b8e192535 X0
               grind)
            | (have r₁ := b8e192535 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e192535 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192535
          have b8e320696 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e81 (σ y) (σ y)
               have i₂ := b8e192542 (σ y)
               grind)
            | exact superpose b8e192542 b8e81
            | exact resolve b8e81 b8e192542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81 b8e192542
          have b8e320718 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e320696
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e320696
            | exact resolve b8e320696 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e320696
          have b8e322091 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e320718
               grind)
            | exact superpose b8e320718 b8e20
            | exact resolve b8e20 b8e320718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e320718
          have b8e322131 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e322091
               have i₂ := b8e191552
               grind)
            | exact superpose b8e191552 b8e322091
            | exact resolve b8e322091 b8e191552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322091
          have b8e322132 : (σ y) = (σ (M.op y y)) := by grind
          clear b8e322131
          have b8e323578 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e322132
               grind)
            | exact superpose b8e322132 b8e14
            | exact resolve b8e14 b8e322132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322132
          have b8e323664 : y = (M.op y y) := by
            first
            | (have i₁ := b8e323578
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e323578
            | exact resolve b8e323578 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e323578
          have b8e325154 : y = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b8e192007 y
               have i₂ := b8e323664
               grind)
            | exact superpose b8e323664 b8e192007
            | exact resolve b8e192007 b8e323664
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192007 b8e323664
          have b8e325419 : y = (M.op y x) := by
            first
            | (have i₁ := b8e325154
               have i₂ := b8e191552
               grind)
            | exact superpose b8e191552 b8e325154
            | exact resolve b8e325154 b8e191552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e191552 b8e325154
          have b8e325455 : False := by grind
          exact b8e325455
