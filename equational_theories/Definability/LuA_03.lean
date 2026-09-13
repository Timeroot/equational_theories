import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e159 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e31 X0 x x X0
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e31
        | exact resolve b0e31 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e164 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e159 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e159
        | exact resolve b0e159 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e165 : y = (M.op x y) := by
        first
        | (have i₁ := b0e159 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e159
        | exact resolve b0e159 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159
      have b0e215 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e164
           grind)
        | exact superpose b0e164 b0e18
        | exact resolve b0e18 b0e164
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164
      have b0e222 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e215
           have i₂ := b0e165
           grind)
        | exact superpose b0e165 b0e215
        | exact resolve b0e215 b0e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e165 b0e215
      have b0e223 : False := by grind
      exact b0e223
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
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
        have b1e39 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) := by
          intro X0
          first
          | (have i₁ := b1e12 y y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
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
        have b1e43 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e41 X0
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e41
          | exact resolve b1e41 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e44 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
          intro X0
          first
          | (have i₁ := b1e39 X0
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e39
          | exact resolve b1e39 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e51 : (M.op y x) = (k x y) := by grind
        have b1e52 : (M.op y y) = (k y y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e51
          | exact resolve b1e51 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e53 : x = (k y y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e52
          | exact resolve b1e52 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e54 : y = (k y y) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e53
          | exact resolve b1e53 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e53
        have b1e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e87 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e43 (M.op y X0)
             have i₂ := b1e44 X0
             grind)
          | exact superpose b1e44 b1e43
          | exact resolve b1e43 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e110 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b1e44 X0
             have i₂ := b1e87 X0
             grind)
          | exact superpose b1e87 b1e44
          | exact resolve b1e44 b1e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e87
        have b1e123 : ∀ X0 : G, (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e43 X0
             have i₂ := b1e110 X0
             grind)
          | exact superpose b1e110 b1e43
          | exact resolve b1e43 b1e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e162 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e110 X0
             have i₂ := b1e123 X0
             grind)
          | exact superpose b1e123 b1e110
          | exact resolve b1e110 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e110 b1e123
        have b1e267 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e57 y
             grind)
          | exact superpose b1e57 b1e26
          | (have j1 := b1e57 y
             grind)
          | exact resolve b1e26 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e57
        have b1e282 : (σ (M.op x y)) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e267
             have r₂ := b1e25
             grind)
          | exact resolve b1e267 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e267
        have b1e285 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e282
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e282
          | exact resolve b1e282 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e282
        have b1e288 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e285
             have i₂ := b1e162 x
             grind)
          | exact superpose b1e162 b1e285
          | exact resolve b1e285 b1e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e162 b1e285
        have b1e289 : False := by grind
        exact b1e289
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e44 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e48 (σ X1) (σ X0)
             grind)
          | exact superpose b2e48 b2e18
          | (have j1 := b2e48 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
             grind)
          | exact resolve b2e18 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e103 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e28 X0 x x X0
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e107 : y = (M.op x y) := by
          first
          | (have i₁ := b2e103 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e103
          | exact resolve b2e103 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103
        have b2e818 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e73 x y
             grind)
          | exact superpose b2e73 b2e19
          | (have j1 := b2e73 x y
             grind)
          | exact resolve b2e19 b2e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e828 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e818
             have r₂ := b2e22
             grind)
          | exact resolve b2e818 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e818
        have b2e831 : (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e828
             have i₂ := b2e107
             grind)
          | exact superpose b2e107 b2e828
          | exact resolve b2e828 b2e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e828
        have b2e832 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e831
             have i₂ := b2e48 y x
             grind)
          | exact superpose b2e48 b2e831
          | (have j1 := b2e48 x y
             grind)
          | (have r₁ := b2e831
             have r₂ := b2e48 (σ y) (σ (k y x))
             grind)
          | (have r₁ := b2e831
             have r₂ := b2e48 (σ (k y x)) (σ y)
             grind)
          | exact resolve b2e831 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e831
        have b2e836 : (σ y) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e832
             have i₂ := b2e107
             grind)
          | exact superpose b2e107 b2e832
          | exact resolve b2e832 b2e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e107 b2e832
        have b2e837 : x = y := by grind
        clear b2e836
        have b2e843 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e837
             grind)
          | exact superpose b2e837 b2e22
          | exact resolve b2e22 b2e837
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e837
        have b2e865 : False := by grind
        exact b2e865
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : (σ y) ≠ (σ (M.op y y)) := by grind
        have b3e47 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e49 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e47
          | exact resolve b3e47 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e50 : (σ y) = (σ (k y y)) := by grind
        clear b3e49
        have b3e61 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b3e50
        have b3e62 : y = (M.op y y) := by
          first
          | (have r₁ := b3e61
             have r₂ := b3e28
             grind)
          | exact resolve b3e61 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e61
        have b3e65 : False := by grind
        exact b3e65
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op y y) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e171 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e60
          have b4e187 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e171
          have b4e190 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e187
          have b4e191 : y = (M.op y y) := by grind
          clear b4e190
          have b4e192 : False := by grind
          exact b4e192
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : False := by grind
          exact b5e31
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 := by
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
        have b6e35 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
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
        have b6e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b6e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e66 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e125 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e28 X0 x x X0
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e28
          | exact resolve b6e28 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e129 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e125 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e125
          | exact resolve b6e125 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e134 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0) X0
             have i₂ := b6e125 X0
             grind)
          | exact superpose b6e125 b6e12
          | exact resolve b6e12 b6e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e163 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e129
             grind)
          | exact superpose b6e129 b6e19
          | exact resolve b6e19 b6e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e129
        have b6e200 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e48 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e48
          | exact resolve b6e48 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e360 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e134 (σ y) (σ x)
             have i₂ := b6e29 (σ y)
             grind)
          | exact superpose b6e29 b6e134
          | exact resolve b6e134 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29 b6e134
        have b6e372 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e200
             grind)
          | exact superpose b6e200 b6e13
          | exact resolve b6e13 b6e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e200
        have b6e385 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e372
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e372
          | exact resolve b6e372 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e372
        have b6e388 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e36
             have i₂ := b6e360
             grind)
          | exact superpose b6e360 b6e36
          | exact resolve b6e36 b6e360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36 b6e360
        have b6e435 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e388
             grind)
          | exact superpose b6e388 b6e13
          | exact resolve b6e13 b6e388
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e388
        have b6e448 : x = (k x y) := by
          first
          | (have i₁ := b6e435
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e435
          | exact resolve b6e435 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e435
        have b6e479 : x = (M.op y x) ∨ x = y := by
          first
          | (have i₁ := b6e66 x y
             have i₂ := b6e448
             grind)
          | exact superpose b6e448 b6e66
          | (have j0 := b6e66 x (M.op y x)
             grind)
          | exact resolve b6e66 b6e448
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66 b6e448
        have b6e482 : x = (M.op y x) := by
          first
          | (have r₁ := b6e479
             have r₂ := b6e21
             grind)
          | exact resolve b6e479 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e479
        have b6e512 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 y x
             have i₂ := b6e482
             grind)
          | exact superpose b6e482 b6e12
          | exact resolve b6e12 b6e482
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e811 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e385
        have b6e812 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e811
             have r₂ := b6e20
             grind)
          | exact resolve b6e811 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e811
        have b6e870 : y = (M.op (M.op y x) y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e512 y
             have i₂ := b6e812
             grind)
          | exact superpose b6e812 b6e512
          | exact resolve b6e512 b6e812
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e512 b6e812
        have b6e889 : y = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e870
             have i₂ := b6e482
             grind)
          | exact superpose b6e482 b6e870
          | exact resolve b6e870 b6e482
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e482 b6e870
        have b6e925 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e163
             have i₂ := b6e889
             grind)
          | exact superpose b6e889 b6e163
          | exact resolve b6e163 b6e889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e163 b6e889
        have b6e935 : (σ x) = (σ y) := by grind
        clear b6e925
        have b6e1009 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e935
             grind)
          | exact superpose b6e935 b6e13
          | exact resolve b6e13 b6e935
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e935
        have b6e1041 : x = y := by
          first
          | (have i₁ := b6e1009
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1009
          | exact resolve b6e1009 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1009
        have b6e1048 : False := by grind
        exact b6e1048
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : x = y := by
            first
            | (have i₁ := b7e29
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e29
            | exact resolve b7e29 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e31 : False := by grind
          exact b7e31
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e88 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e84 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e91 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e28 X0 X1
               have i₂ := b8e88 X1 (τ X0)
               grind)
            | exact superpose b8e88 b8e28
            | (have j1 := b8e88 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e28 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28
          have b8e92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e88 (σ X1) (σ X0)
               grind)
            | exact superpose b8e88 b8e19
            | (have j1 := b8e88 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e336 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e91 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e91
            | exact resolve b8e91 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e358 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e336 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e336
            | (have j0 := b8e336 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e336 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e336
          have b8e756 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e92 x y
               grind)
            | exact superpose b8e92 b8e20
            | (have j1 := b8e92 x y
               grind)
            | exact resolve b8e20 b8e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e775 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e756
               have r₂ := b8e24
               grind)
            | exact resolve b8e756 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e756
          have b8e780 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e775
               have i₂ := b8e358 x y
               grind)
            | exact superpose b8e358 b8e775
            | (have j1 := b8e358 x y
               grind)
            | (have r₁ := b8e775
               have r₂ := b8e358 x y
               grind)
            | (have r₁ := b8e775
               have r₂ := b8e358 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e775
               have r₂ := b8e358 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e775 b8e358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358 b8e775
          have b8e781 : x = y := by grind
          clear b8e780
          have b8e784 : False := by grind
          exact b8e784

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
        intro X0
        first
        | (have i₁ := b0e11 y y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
      have b0e31 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
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
      have b0e46 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e30 (M.op y X0)
           have i₂ := b0e27 X0
           grind)
        | exact superpose b0e27 b0e30
        | exact resolve b0e30 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
        intro X0
        first
        | (have i₁ := b0e27 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e27
        | exact resolve b0e27 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e46
      have b0e89 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e30 X0
           have i₂ := b0e75 X0
           grind)
        | exact superpose b0e75 b0e30
        | exact resolve b0e30 b0e75
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e100 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e75 X0
           have i₂ := b0e89 X0
           grind)
        | exact superpose b0e89 b0e75
        | exact resolve b0e75 b0e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e107 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1
           have i₂ := b0e89 X0
           grind)
        | exact superpose b0e89 b0e11
        | exact resolve b0e11 b0e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e107 X0 X1
           have i₂ := b0e89 X1
           grind)
        | exact superpose b0e89 b0e107
        | exact resolve b0e107 b0e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89 b0e107
      have b0e262 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e110 (M.op (M.op (σ y) X0) (σ y)) X0
           have i₂ := b0e31 X0
           grind)
        | exact superpose b0e31 b0e110
        | exact resolve b0e110 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e283 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e262 x
           have i₂ := b0e110 (σ y) x
           grind)
        | exact superpose b0e110 b0e262
        | exact resolve b0e262 b0e110
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e110 b0e262
      have b0e398 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e283 (σ x)
           grind)
        | exact superpose b0e283 b0e18
        | exact resolve b0e18 b0e283
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e283
      have b0e406 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e398
           have i₂ := b0e100 x
           grind)
        | exact superpose b0e100 b0e398
        | exact resolve b0e398 b0e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100 b0e398
      have b0e407 : False := by grind
      exact b0e407
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
          intro X0
          first
          | (have i₁ := b1e12 y y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
        have b1e36 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
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
        have b1e37 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b1e36 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e38 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e41 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e38
        have b1e42 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e41
             have r₂ := b1e21
             grind)
          | exact resolve b1e41 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e42
          | exact resolve b1e42 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e44 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e37 x
             grind)
          | exact superpose b1e37 b1e43
          | exact resolve b1e43 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e43
        have b1e46 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e29 (M.op y X0)
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e29
          | exact resolve b1e29 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b1e26 X0
             have i₂ := b1e46 X0
             grind)
          | exact superpose b1e46 b1e26
          | exact resolve b1e26 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e46
        have b1e76 : ∀ X0 : G, (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e29 X0
             have i₂ := b1e62 X0
             grind)
          | exact superpose b1e62 b1e29
          | exact resolve b1e29 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e89 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e62 X0
             have i₂ := b1e76 X0
             grind)
          | exact superpose b1e76 b1e62
          | exact resolve b1e62 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e76
        have b1e102 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e44
             grind)
          | exact superpose b1e44 b1e21
          | exact resolve b1e21 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e112 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e102
             have i₂ := b1e89 x
             grind)
          | exact superpose b1e89 b1e102
          | exact resolve b1e102 b1e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89 b1e102
        have b1e113 : False := by grind
        exact b1e113
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e33 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
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
        have b2e34 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b2e33 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e464 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e44 x y
             grind)
          | exact superpose b2e44 b2e19
          | (have j1 := b2e44 y y
             grind)
          | exact resolve b2e19 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e509 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e464
             have r₂ := b2e21
             grind)
          | exact resolve b2e464 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e464
        have b2e517 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e509
             have r₂ := b2e22
             grind)
          | exact resolve b2e509 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e509
        have b2e521 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e517
             have i₂ := b2e34 x
             grind)
          | exact superpose b2e34 b2e517
          | exact resolve b2e517 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e517
        have b2e522 : False := by grind
        exact b2e522
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e35 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
        have b3e36 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e61 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e36 (σ X0)
             grind)
          | exact superpose b3e36 b3e18
          | exact resolve b3e18 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e82 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e61 y
             grind)
          | exact superpose b3e61 b3e22
          | exact resolve b3e22 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e104 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e82
             grind)
          | exact superpose b3e82 b3e13
          | exact resolve b3e13 b3e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e106 : y = (k y y) := by
          first
          | (have i₁ := b3e104
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e104
          | exact resolve b3e104 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104
        have b3e123 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e106
             grind)
          | exact superpose b3e106 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e124 : y = (M.op y y) := by grind
        clear b3e123
        have b3e126 : False := by grind
        exact b3e126
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) := by
            intro X0
            first
            | (have i₁ := b5e13 y x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
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
          have b5e32 : y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b5e28 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e89 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29 X0 x x X0
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e29
            | exact resolve b5e29 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e102 : x = (M.op x x) := by
            first
            | (have i₁ := b5e30 x
               have i₂ := b5e89 x
               grind)
            | exact superpose b5e89 b5e30
            | exact resolve b5e30 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e89
          have b5e134 : y = (M.op x y) := by
            first
            | (have i₁ := b5e32
               have i₂ := b5e102
               grind)
            | exact superpose b5e102 b5e32
            | exact resolve b5e32 b5e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e102
          have b5e150 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e134
               grind)
            | exact superpose b5e134 b5e22
            | exact resolve b5e22 b5e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e184 : y = (M.op y y) := by
            first
            | (have i₁ := b5e134
               have i₂ := b5e150
               grind)
            | exact superpose b5e150 b5e134
            | exact resolve b5e134 b5e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e134 b5e150
          have b5e185 : False := by grind
          exact b5e185
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e33 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
        have b6e34 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e33 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e36 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e34 (σ X0)
             grind)
          | exact superpose b6e34 b6e18
          | exact resolve b6e18 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e77 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e36 y
             grind)
          | exact superpose b6e36 b6e22
          | exact resolve b6e22 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e103 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e77
             grind)
          | exact superpose b6e77 b6e13
          | exact resolve b6e13 b6e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e105 : y = (k y y) := by
          first
          | (have i₁ := b6e103
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e103
          | exact resolve b6e103 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e103
        have b6e136 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e105
             grind)
          | exact superpose b6e105 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e105
        have b6e137 : y = (M.op y y) := by grind
        clear b6e136
        have b6e139 : False := by grind
        exact b6e139
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
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
          have b7e79 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e34 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e119 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0 x x X0
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e33
            | exact resolve b7e33 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e133 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e34 (σ x)
               have i₂ := b7e119 (σ x)
               grind)
            | exact superpose b7e119 b7e34
            | exact resolve b7e34 b7e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e119
          have b7e565 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e79
               have i₂ := b7e133
               grind)
            | exact superpose b7e133 b7e79
            | exact resolve b7e79 b7e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e133
          have b7e922 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e565
               grind)
            | exact superpose b7e565 b7e24
            | exact resolve b7e24 b7e565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1038 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e565
               have i₂ := b7e922
               grind)
            | exact superpose b7e922 b7e565
            | exact resolve b7e565 b7e922
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e565 b7e922
          have b7e1070 : False := by grind
          exact b7e1070
        · have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e68 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
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
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e68 X0 X2 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e180 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e74 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e181 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e180 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180
          have b8e392 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e63 x y
               grind)
            | exact superpose b8e63 b8e20
            | (have j1 := b8e63 y y
               grind)
            | exact resolve b8e20 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e445 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e392
               have r₂ := b8e23
               grind)
            | exact resolve b8e392 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e392
          have b8e449 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e445
               have r₂ := b8e24
               grind)
            | exact resolve b8e445 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e445
          have b8e450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e449
               have i₂ := b8e181 x y
               grind)
            | exact superpose b8e181 b8e449
            | (have j1 := b8e181 x y
               grind)
            | exact resolve b8e449 b8e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181 b8e449
          have b8e457 : x = (M.op x y) := by grind
          clear b8e450
          have b8e460 : False := by grind
          exact b8e460

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e28 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
        intro X0
        first
        | (have i₁ := b0e11 y y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
      have b0e32 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
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
      have b0e49 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e31 (M.op y X0)
           have i₂ := b0e28 X0
           grind)
        | exact superpose b0e28 b0e31
        | exact resolve b0e31 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
        intro X0
        first
        | (have i₁ := b0e28 X0
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e28
        | exact resolve b0e28 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e49
      have b0e91 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e31 X0
           have i₂ := b0e79 X0
           grind)
        | exact superpose b0e79 b0e31
        | exact resolve b0e31 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e100 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e79 X0
           have i₂ := b0e91 X0
           grind)
        | exact superpose b0e91 b0e79
        | exact resolve b0e79 b0e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e106 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1
           have i₂ := b0e91 X0
           grind)
        | exact superpose b0e91 b0e11
        | exact resolve b0e11 b0e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e109 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e106 X0 X1
           have i₂ := b0e91 X1
           grind)
        | exact superpose b0e91 b0e106
        | exact resolve b0e106 b0e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91 b0e106
      have b0e255 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
        intro X0
        first
        | (have i₁ := b0e109 (M.op (M.op (σ y) X0) (σ y)) X0
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e109
        | exact resolve b0e109 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e275 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e255 x
           have i₂ := b0e109 (σ y) x
           grind)
        | exact superpose b0e109 b0e255
        | exact resolve b0e255 b0e109
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109 b0e255
      have b0e420 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e275 (σ x)
           grind)
        | exact superpose b0e275 b0e18
        | exact resolve b0e18 b0e275
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e275
      have b0e428 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e420
           have i₂ := b0e100 x
           grind)
        | exact superpose b0e100 b0e420
        | exact resolve b0e420 b0e100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e100 b0e420
      have b0e429 : False := by grind
      exact b0e429
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
          intro X0
          first
          | (have i₁ := b1e12 y y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
        have b1e45 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
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
        have b1e46 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b1e45 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e53 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e39 (M.op y X0)
             have i₂ := b1e37 X0
             grind)
          | exact superpose b1e37 b1e39
          | exact resolve b1e39 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e70 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b1e37 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e37
          | exact resolve b1e37 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e53
        have b1e88 : ∀ X0 : G, (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e39 X0
             have i₂ := b1e70 X0
             grind)
          | exact superpose b1e70 b1e39
          | exact resolve b1e39 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e98 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e70 X0
             have i₂ := b1e88 X0
             grind)
          | exact superpose b1e88 b1e70
          | exact resolve b1e70 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70 b1e88
        have b1e252 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e49 y
             grind)
          | exact superpose b1e49 b1e24
          | (have j1 := b1e49 y
             grind)
          | exact resolve b1e24 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e49
        have b1e265 : (σ (M.op x y)) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e252
             have r₂ := b1e21
             grind)
          | exact resolve b1e252 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e252
        have b1e268 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e265
             have i₂ := b1e46 y
             grind)
          | exact superpose b1e46 b1e265
          | exact resolve b1e265 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e265
        have b1e271 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e268
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e268
          | exact resolve b1e268 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e268
        have b1e274 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e271
             have i₂ := b1e98 x
             grind)
          | exact superpose b1e98 b1e271
          | exact resolve b1e271 b1e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e98 b1e271
        have b1e275 : False := by grind
        exact b1e275
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e26 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
          intro X0
          first
          | (have i₁ := b2e12 y y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
        have b2e34 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k X0 y) := by
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
        have b2e35 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e39 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e28 (M.op y X0)
             have i₂ := b2e26 X0
             grind)
          | exact superpose b2e26 b2e28
          | exact resolve b2e28 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b2e26 X0
             have i₂ := b2e39 X0
             grind)
          | exact superpose b2e39 b2e26
          | exact resolve b2e26 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e39
        have b2e60 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 y
             have i₂ := b2e35 (τ X0)
             grind)
          | exact superpose b2e35 b2e24
          | exact resolve b2e24 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e35
        have b2e69 : ∀ X0 : G, (M.op y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e28 X0
             have i₂ := b2e54 X0
             grind)
          | exact superpose b2e54 b2e28
          | exact resolve b2e28 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e54
        have b2e341 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e60 X0
             have i₂ := b2e69 (τ X0)
             grind)
          | exact superpose b2e69 b2e60
          | exact resolve b2e60 b2e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60 b2e69
        have b2e350 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e341 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e341
          | exact resolve b2e341 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e341
        have b2e402 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e350
        have b2e409 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e402
        have b2e415 : False := by grind
        exact b2e415
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) ≠ (σ (M.op y y)) := by grind
        have b3e44 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b3e45 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e44 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e47 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e45 (σ X0)
             grind)
          | exact superpose b3e45 b3e18
          | exact resolve b3e18 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e104 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e47 y
             grind)
          | exact superpose b3e47 b3e22
          | exact resolve b3e22 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e119 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b3e104
        have b3e132 : y = (M.op y y) := by
          first
          | (have r₁ := b3e119
             have r₂ := b3e25
             grind)
          | exact resolve b3e119 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e119
        have b3e134 : False := by grind
        exact b3e134
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e193 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e53 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e53
            | exact resolve b4e53 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e196 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e53
          have b4e210 : (σ (M.op y y)) ≠ (σ (k y y)) := by
            first
            | (have r₁ := b4e196
               have r₂ := b4e23
               grind)
            | exact resolve b4e196 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196
          have b4e211 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e193 X0
               have i₂ := b4e29 X0 (τ X0)
               grind)
            | exact superpose b4e29 b4e193
            | (have j0 := b4e193 X0
               grind)
            | exact resolve b4e193 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e193
          have b4e212 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e211 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e211
            | (have j0 := b4e211 X0
               grind)
            | exact resolve b4e211 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e211
          have b4e213 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e212 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e212 x
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e212 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e212
          have b4e265 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e210
               have i₂ := b4e213 y
               grind)
            | exact superpose b4e213 b4e210
            | exact resolve b4e210 b4e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210 b4e213
          have b4e270 : False := by grind
          exact b4e270
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : False := by grind
          exact b5e28
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e34 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b6e35 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e34 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e37 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e35 (σ X0)
             grind)
          | exact superpose b6e35 b6e18
          | exact resolve b6e18 b6e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e84 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e37 y
             grind)
          | exact superpose b6e37 b6e22
          | exact resolve b6e22 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e104 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e84
             grind)
          | exact superpose b6e84 b6e13
          | exact resolve b6e13 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e105 : y = (k y y) := by
          first
          | (have i₁ := b6e104
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e104
          | exact resolve b6e104 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e135 : y = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b6e105
        have b6e136 : y = (M.op y y) := by grind
        clear b6e135
        have b6e138 : False := by grind
        exact b6e138
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e28 : x = y := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e27
            | exact resolve b7e27 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e29 : False := by grind
          exact b7e29
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e80 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
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
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e80 X0 X2 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e179 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e84 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e180 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e179 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e179
          have b8e184 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e180 (σ X1) (σ X0)
               grind)
            | exact superpose b8e180 b8e19
            | (have j1 := b8e180 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e186 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e180 (τ X1) X0
               grind)
            | exact superpose b8e180 b8e26
            | (have j1 := b8e180 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
               grind)
            | exact resolve b8e26 b8e180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e180
          have b8e3457 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e186 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e186
            | exact resolve b8e186 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e3559 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e3457 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e3457
            | (have j0 := b8e3457 (σ (k X0 X1)) (σ (M.op X1 X0))
               grind)
            | exact resolve b8e3457 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3457
          have b8e9064 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e184 x y
               grind)
            | exact superpose b8e184 b8e20
            | (have j1 := b8e184 x y
               grind)
            | exact resolve b8e20 b8e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e184
          have b8e9140 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e9064
               have r₂ := b8e24
               grind)
            | exact resolve b8e9064 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9064
          have b8e9337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e9140
               have i₂ := b8e3559 y x
               grind)
            | exact superpose b8e3559 b8e9140
            | (have j1 := b8e3559 x y
               grind)
            | (have r₁ := b8e9140
               have r₂ := b8e3559 y x
               grind)
            | (have r₁ := b8e9140
               have r₂ := b8e3559 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e9140
               have r₂ := b8e3559 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e9140 b8e3559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3559 b8e9140
          have b8e9338 : x = y := by grind
          clear b8e9337
          have b8e9343 : False := by grind
          exact b8e9343

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e40 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) := by
            intro X0
            first
            | (have i₁ := b5e13 y x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
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
          have b5e44 : y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b5e40 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e40
            | exact resolve b5e40 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e108 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e41 X0 x x X0
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e41
            | exact resolve b5e41 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e115 : x = (M.op x x) := by
            first
            | (have i₁ := b5e42 x
               have i₂ := b5e108 x
               grind)
            | exact superpose b5e108 b5e42
            | exact resolve b5e42 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e108
          have b5e149 : y = (M.op x y) := by
            first
            | (have i₁ := b5e44
               have i₂ := b5e115
               grind)
            | exact superpose b5e115 b5e44
            | exact resolve b5e44 b5e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e115
          have b5e159 : x = y := by
            first
            | (have i₁ := b5e149
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e149
            | exact resolve b5e149 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149
          have b5e160 : False := by grind
          exact b5e160
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
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
          have b7e99 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e35 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e104 : (σ y) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b7e99
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e99
            | exact resolve b7e99 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e155 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 X0 x x X0
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e163 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e35 (σ x)
               have i₂ := b7e155 (σ x)
               grind)
            | exact superpose b7e155 b7e35
            | exact resolve b7e35 b7e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e155
          have b7e169 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e163
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e163
            | exact resolve b7e163 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e163
          have b7e299 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e104
               have i₂ := b7e169
               grind)
            | exact superpose b7e169 b7e104
            | exact resolve b7e104 b7e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104 b7e169
          have b7e318 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e299
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e299
            | exact resolve b7e299 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e299
          have b7e322 : False := by grind
          exact b7e322
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e118 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e131 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e118
               have r₂ := b8e24
               grind)
            | exact resolve b8e118 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e135 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e131
               have r₂ := b8e23
               grind)
            | exact resolve b8e131 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e137 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e135
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e135
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e135
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e135
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e135 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e138 : x = (M.op x y) ∨ x = y := by grind
          clear b8e137
          have b8e139 : x = y := by
            first
            | (have r₁ := b8e138
               have r₂ := b8e22
               grind)
            | exact resolve b8e138 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e140 : False := by grind
          exact b8e140

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
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
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b4e38 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b4e32 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e143 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 X0 x x X0
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e152 : y = (M.op y y) := by
            first
            | (have i₁ := b4e35 y
               have i₂ := b4e143 y
               grind)
            | exact superpose b4e143 b4e35
            | exact resolve b4e35 b4e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e143
          have b4e193 : x = (M.op y x) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e152
               grind)
            | exact superpose b4e152 b4e38
            | exact resolve b4e38 b4e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e152
          have b4e203 : x = y := by
            first
            | (have i₁ := b4e193
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e193
            | exact resolve b4e193 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193
          have b4e204 : False := by grind
          exact b4e204
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
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
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b5e32 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e94 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 X0 x x X0
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e101 : y = (M.op y y) := by
            first
            | (have i₁ := b5e34 y
               have i₂ := b5e94 y
               grind)
            | exact superpose b5e94 b5e34
            | exact resolve b5e34 b5e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e94
          have b5e135 : x = (M.op y x) := by
            first
            | (have i₁ := b5e36
               have i₂ := b5e101
               grind)
            | exact superpose b5e101 b5e36
            | exact resolve b5e36 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e101
          have b5e145 : x = y := by
            first
            | (have i₁ := b5e135
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e135
            | exact resolve b5e135 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e135
          have b5e146 : False := by grind
          exact b5e146
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
          have b7e45 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b7e43
          have b7e46 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (k (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e46
            | exact resolve b7e46 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (σ (M.op y y)) = (σ (k x y)) := by
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
          have b7e51 : (k x y) = (τ (σ (M.op y y))) := by
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
          have b7e52 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e51
            | exact resolve b7e51 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) ∨ x = y := by
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
          have b7e63 : (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e65 : (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e79 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e22
            | exact resolve b7e22 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e141 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0 x x X0
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e33
            | exact resolve b7e33 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e148 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e34 (σ y)
               have i₂ := b7e141 (σ y)
               grind)
            | exact superpose b7e141 b7e34
            | exact resolve b7e34 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e141
          have b7e154 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e148
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e148
            | exact resolve b7e148 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e148
          have b7e185 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e154
               grind)
            | exact superpose b7e154 b7e14
            | exact resolve b7e14 b7e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e154
          have b7e186 : y = (M.op y y) := by
            first
            | (have i₁ := b7e185
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e185
            | exact resolve b7e185 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e185
          have b7e191 : False := by grind
          exact b7e191
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          clear b8e26
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 X0 x x X0
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e77 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0) X0
               have i₂ := b8e68 X0
               grind)
            | exact superpose b8e68 b8e13
            | exact resolve b8e13 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e119 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e128 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e131 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e119
               have r₂ := b8e23
               grind)
            | exact resolve b8e119 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e136 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          clear b8e38
          have b8e401 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 (M.op X0 X1)
               have i₂ := b8e13 X0 X0 X1
               grind)
            | exact superpose b8e13 b8e77
            | exact resolve b8e77 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e574 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e131
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e131
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e131
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e131
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e131 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e575 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e574
          have b8e576 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e575
               have r₂ := b8e21
               grind)
            | exact resolve b8e575 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e575
          have b8e754 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e576
               grind)
            | exact superpose b8e576 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e576
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e576
               grind)
            | exact resolve b8e17 b8e576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e763 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e401 (σ x) (σ y)
               have i₂ := b8e576
               grind)
            | exact superpose b8e576 b8e401
            | exact resolve b8e401 b8e576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e576
          have b8e764 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e754
          have b8e765 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e763
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e763
            | exact resolve b8e763 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e763
          have b8e769 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e764
               have r₂ := b8e23
               grind)
            | exact resolve b8e764 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e764
          have b8e777 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e769
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e769
            | exact resolve b8e769 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e769
          have b8e779 : (σ (k y x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e777
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e777
            | exact resolve b8e777 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e777
          have b8e932 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e765
               grind)
            | exact superpose b8e765 b8e14
            | exact resolve b8e14 b8e765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e765
          have b8e968 : x = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e932
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e932
            | exact resolve b8e932 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e932
          have b8e1749 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e128 (τ X1) (τ X0)
               have i₂ := b8e136 X1 X0
               grind)
            | exact superpose b8e136 b8e128
            | (have j0 := b8e128 (τ X1) (τ X0)
               grind)
            | exact resolve b8e128 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128 b8e136
          have b8e1756 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1749 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e1749
            | (have j0 := b8e1749 X0 X1
               grind)
            | exact resolve b8e1749 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1749
          have b8e1759 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1756 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e1756
            | (have j0 := b8e1756 X0 X1
               grind)
            | exact resolve b8e1756 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1756
          have b8e1761 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1759 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1759
            | (have j0 := b8e1759 X0 X1
               grind)
            | exact resolve b8e1759 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1759
          have b8e1762 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1761 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1761
            | (have j0 := b8e1761 X0 X1
               grind)
            | exact resolve b8e1761 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1761
          have b8e1763 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1762 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e1762
            | (have j0 := b8e1762 X0 X1
               grind)
            | exact resolve b8e1762 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1762
          have b8e1764 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1763 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1763
            | (have j0 := b8e1763 X0 X1
               grind)
            | exact resolve b8e1763 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1763
          have b8e3129 : (k y x) = (τ (σ (M.op x x))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e779
               grind)
            | exact superpose b8e779 b8e14
            | exact resolve b8e14 b8e779
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e779
          have b8e3171 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3129
               have i₂ := b8e14 (M.op x x)
               grind)
            | exact superpose b8e14 b8e3129
            | exact resolve b8e3129 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3129
          have b8e3336 : x ≠ (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1764 y x
               have i₂ := b8e3171
               grind)
            | exact superpose b8e3171 b8e1764
            | (have j0 := b8e1764 y x
               grind)
            | exact resolve b8e1764 b8e3171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1764 b8e3171
          have b8e3340 : x ≠ (M.op x x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e3336
          have b8e3343 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e3340
               have r₂ := b8e968
               grind)
            | exact resolve b8e3340 b8e968
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e968 b8e3340
          have b8e3345 : x = (M.op x y) := by
            first
            | (have r₁ := b8e3343
               have r₂ := b8e21
               grind)
            | exact resolve b8e3343 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3343
          have b8e3515 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) := by
            intro X0
            first
            | (have i₁ := b8e13 y x X0
               have i₂ := b8e3345
               grind)
            | exact superpose b8e3345 b8e13
            | exact resolve b8e13 b8e3345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3570 : ∀ X0 : G, y = (M.op (M.op x X0) y) := by
            intro X0
            first
            | (have i₁ := b8e3515 X0
               have i₂ := b8e401 x X0
               grind)
            | exact superpose b8e401 b8e3515
            | exact resolve b8e3515 b8e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e401 b8e3515
          have b8e4081 : y = (M.op x y) := by
            first
            | (have i₁ := b8e3570 y
               have i₂ := b8e3345
               grind)
            | exact superpose b8e3345 b8e3570
            | exact resolve b8e3570 b8e3345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3570
          have b8e4244 : x = y := by
            first
            | (have i₁ := b8e3345
               have i₂ := b8e4081
               grind)
            | exact superpose b8e4081 b8e3345
            | exact resolve b8e3345 b8e4081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3345 b8e4081
          have b8e4301 : False := by grind
          exact b8e4301

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
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
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b4e38 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b4e32 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e142 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 X0 x x X0
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e151 : y = (M.op y y) := by
            first
            | (have i₁ := b4e35 y
               have i₂ := b4e142 y
               grind)
            | exact superpose b4e142 b4e35
            | exact resolve b4e35 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e142
          have b4e192 : x = (M.op y x) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e151
               grind)
            | exact superpose b4e151 b4e38
            | exact resolve b4e38 b4e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e151
          have b4e202 : x = y := by
            first
            | (have i₁ := b4e192
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e192
            | exact resolve b4e192 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e192
          have b4e203 : False := by grind
          exact b4e203
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
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
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b5e32 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e94 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 X0 x x X0
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e101 : y = (M.op y y) := by
            first
            | (have i₁ := b5e34 y
               have i₂ := b5e94 y
               grind)
            | exact superpose b5e94 b5e34
            | exact resolve b5e34 b5e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e94
          have b5e135 : x = (M.op y x) := by
            first
            | (have i₁ := b5e36
               have i₂ := b5e101
               grind)
            | exact superpose b5e101 b5e36
            | exact resolve b5e36 b5e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e101
          have b5e145 : x = y := by
            first
            | (have i₁ := b5e135
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e135
            | exact resolve b5e135 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e135
          have b5e146 : False := by grind
          exact b5e146
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
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
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e97 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
            first
            | (have i₁ := b7e34 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e102 : (σ x) = (M.op (σ (M.op y y)) (σ x)) := by
            first
            | (have i₁ := b7e97
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e97
            | exact resolve b7e97 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e134 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0 x x X0
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e33
            | exact resolve b7e33 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e141 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e34 (σ y)
               have i₂ := b7e134 (σ y)
               grind)
            | exact superpose b7e134 b7e34
            | exact resolve b7e34 b7e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e134
          have b7e147 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e141
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e141
            | exact resolve b7e141 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e141
          have b7e328 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e102
               have i₂ := b7e147
               grind)
            | exact superpose b7e147 b7e102
            | exact resolve b7e102 b7e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102 b7e147
          have b7e348 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e328
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e328
            | exact resolve b7e328 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e328
          have b7e350 : False := by grind
          exact b7e350
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
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
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
               have i₂ := b8e13 X0 X1 X2
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
          have b8e48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e56 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e18 (τ X1) X0
               grind)
            | exact superpose b8e18 b8e26
            | (have j1 := b8e18 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e60 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 X0 x x X0
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e72 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e68 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e68
            | exact resolve b8e68 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0) X0
               have i₂ := b8e68 X0
               grind)
            | exact superpose b8e68 b8e13
            | exact resolve b8e13 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X2) X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 X1 (σ X0) (σ X0) X2
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e33
            | exact resolve b8e33 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e119 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e128 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e130 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e119
               have r₂ := b8e23
               grind)
            | exact resolve b8e119 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e133 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          clear b8e38
          have b8e148 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e40 X0
               grind)
            | exact superpose b8e40 b8e14
            | exact resolve b8e14 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e398 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 (M.op X0 X1)
               have i₂ := b8e13 X0 X0 X1
               grind)
            | exact superpose b8e13 b8e77
            | exact resolve b8e77 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e399 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e77 (σ X0) (σ (M.op X0 X0))
               have i₂ := b8e60 X0 (σ X0)
               grind)
            | exact superpose b8e60 b8e77
            | exact resolve b8e77 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60 b8e77
          have b8e447 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e398 (τ X0) (τ X0)
               have i₂ := b8e148 X0
               grind)
            | exact superpose b8e148 b8e398
            | exact resolve b8e398 b8e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e571 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e130
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e130
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e130
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e130
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e130 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e572 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e571
          have b8e573 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e572
               have r₂ := b8e21
               grind)
            | exact resolve b8e572 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e572
          have b8e751 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e573
               grind)
            | exact superpose b8e573 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e573
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e573
               grind)
            | exact resolve b8e17 b8e573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e760 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e398 (σ x) (σ y)
               have i₂ := b8e573
               grind)
            | exact superpose b8e573 b8e398
            | exact resolve b8e398 b8e573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e573
          have b8e761 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e751
          have b8e762 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e760
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e760
            | exact resolve b8e760 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e760
          have b8e766 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e761
               have r₂ := b8e23
               grind)
            | exact resolve b8e761 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e761
          have b8e774 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e766
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e766
            | exact resolve b8e766 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e766
          have b8e923 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e774
               grind)
            | exact superpose b8e774 b8e14
            | exact resolve b8e14 b8e774
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e774
          have b8e960 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e923
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e923
            | exact resolve b8e923 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e923
          have b8e1073 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e18 y x
               have i₂ := b8e960
               grind)
            | exact superpose b8e960 b8e18
            | (have j0 := b8e18 y x
               grind)
            | exact resolve b8e18 b8e960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e960
          have b8e1074 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e1073
          have b8e1076 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e1074
               have r₂ := b8e21
               grind)
            | exact resolve b8e1074 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1074
          have b8e1173 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 y x X0
               have i₂ := b8e1076
               grind)
            | exact superpose b8e1076 b8e13
            | exact resolve b8e13 b8e1076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1191 : x = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e398 x y
               have i₂ := b8e1076
               grind)
            | exact superpose b8e1076 b8e398
            | exact resolve b8e398 b8e1076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1076
          have b8e1201 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e1173 X0
               have i₂ := b8e398 x X0
               grind)
            | exact superpose b8e398 b8e1173
            | exact resolve b8e1173 b8e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1173
          have b8e1451 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e762
               grind)
            | exact superpose b8e762 b8e14
            | exact resolve b8e14 b8e762
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e762
          have b8e1487 : x = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1451
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e1451
            | exact resolve b8e1451 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1451
          have b8e1565 : (τ x) = (M.op (τ x) (τ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e447 x
               have i₂ := b8e1487
               grind)
            | exact superpose b8e1487 b8e447
            | exact resolve b8e447 b8e1487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1487
          have b8e1591 : (τ x) = (τ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1565
               have i₂ := b8e148 x
               grind)
            | exact superpose b8e148 b8e1565
            | exact resolve b8e1565 b8e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1565
          have b8e1977 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1201 x
               have i₂ := b8e1191
               grind)
            | exact superpose b8e1191 b8e1201
            | exact resolve b8e1201 b8e1191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1191 b8e1201
          have b8e2011 : y = (M.op x y) := by grind
          clear b8e1977
          have b8e3836 : (M.op (M.op x x) (M.op x x)) = (σ (M.op (τ x) (τ x))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e40 (M.op x x)
               have i₂ := b8e1591
               grind)
            | exact superpose b8e1591 b8e40
            | exact resolve b8e40 b8e1591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3842 : ∀ X0 : G, (τ (k (M.op x x) X0)) = (k (τ x) (τ X0)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e133 X0 (M.op x x)
               have i₂ := b8e1591
               grind)
            | exact superpose b8e1591 b8e133
            | exact resolve b8e133 b8e1591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1591
          have b8e3849 : ∀ X0 : G, (τ (k (M.op x x) X0)) = (τ (k x X0)) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e3842 X0
               have i₂ := b8e133 X0 x
               grind)
            | exact superpose b8e133 b8e3842
            | exact resolve b8e3842 b8e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133 b8e3842
          have b8e3855 : (M.op x x) = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3836
               have i₂ := b8e40 x
               grind)
            | exact superpose b8e40 b8e3836
            | exact resolve b8e3836 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e3836
          have b8e3864 : ∀ X0 : G, x = y ∨ (τ (k (M.op x x) X0)) = (τ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b8e3849 X0
               have i₂ := b8e2011
               grind)
            | exact superpose b8e2011 b8e3849
            | (have j0 := b8e3849 X0
               grind)
            | exact resolve b8e3849 b8e2011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3849
          have b8e3870 : x = y ∨ (M.op x x) = (M.op (M.op x x) (M.op x x)) := by
            first
            | (have i₁ := b8e3855
               have i₂ := b8e2011
               grind)
            | exact superpose b8e2011 b8e3855
            | exact resolve b8e3855 b8e2011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3855
          have b8e3874 : ∀ X0 : G, (τ (k (M.op x x) X0)) = (τ (k x X0)) := by
            intro X0
            first
            | (have j0 := b8e3864 X0
               grind)
            | (have r₁ := b8e3864 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e3864 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3864
          have b8e3878 : (M.op x x) = (M.op (M.op x x) (M.op x x)) := by
            first
            | (have r₁ := b8e3870
               have r₂ := b8e21
               grind)
            | exact resolve b8e3870 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3870
          have b8e3994 : ∀ X0 : G, (k (M.op x x) X0) = (σ (τ (k x X0))) := by
            intro X0
            first
            | (have i₁ := b8e15 (k (M.op x x) X0)
               have i₂ := b8e3874 X0
               grind)
            | exact superpose b8e3874 b8e15
            | exact resolve b8e15 b8e3874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3874
          have b8e4015 : ∀ X0 : G, (k (M.op x x) X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e3994 X0
               have i₂ := b8e15 (k x X0)
               grind)
            | exact superpose b8e15 b8e3994
            | exact resolve b8e3994 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3994
          have b8e4139 : (M.op (M.op x x) (M.op x x)) = (k x (M.op x x)) := by grind
          clear b8e4015
          have b8e4159 : (M.op x x) = (k x (M.op x x)) := by
            first
            | (have i₁ := b8e4139
               have i₂ := b8e3878
               grind)
            | exact superpose b8e3878 b8e4139
            | exact resolve b8e4139 b8e3878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3878 b8e4139
          have b8e4275 : (M.op x x) = (M.op (M.op x x) x) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e18 x (M.op x x)
               have i₂ := b8e4159
               grind)
            | exact superpose b8e4159 b8e18
            | (have j0 := b8e18 x (M.op x x)
               grind)
            | exact resolve b8e18 b8e4159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4282 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e128 (M.op x x) x
               have i₂ := b8e4159
               grind)
            | exact superpose b8e4159 b8e128
            | (have j0 := b8e128 (M.op x x) x
               grind)
            | exact resolve b8e128 b8e4159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128 b8e4159
          have b8e4283 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
          clear b8e4282
          have b8e4284 : (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by grind
          clear b8e4275
          have b8e4286 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e4283
               have i₂ := b8e72 x
               grind)
            | exact superpose b8e72 b8e4283
            | exact resolve b8e4283 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e4283
          have b8e4287 : (σ x) = (σ (M.op x x)) := by grind
          clear b8e4286
          have b8e4297 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e4284
               have i₂ := b8e68 x
               grind)
            | exact superpose b8e68 b8e4284
            | exact resolve b8e4284 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68 b8e4284
          have b8e4298 : x = (M.op x x) := by grind
          clear b8e4297
          have b8e4418 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e13 x x X0
               have i₂ := b8e4298
               grind)
            | exact superpose b8e4298 b8e13
            | exact resolve b8e13 b8e4298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4419 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e4298
               grind)
            | exact superpose b8e4298 b8e13
            | exact resolve b8e13 b8e4298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4298
          have b8e4464 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b8e4418 X0
               have i₂ := b8e398 x X0
               grind)
            | exact superpose b8e398 b8e4418
            | exact resolve b8e4418 b8e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4418
          have b8e4875 : ∀ X0 : G, (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e4419 X0
               have i₂ := b8e4464 X0
               grind)
            | exact superpose b8e4464 b8e4419
            | exact resolve b8e4419 b8e4464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4930 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x (τ X0)) x))) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e56 (M.op (M.op x (τ x)) x) x
               have i₂ := b8e4419 (τ x)
               grind)
            | exact superpose b8e4419 b8e56
            | (have j0 := b8e56 (M.op (M.op x (τ X0)) x) X0
               grind)
            | exact resolve b8e56 b8e4419
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56 b8e4419
          have b8e4931 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x (τ X0)) x))) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have j0 := b8e4930 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4930
          have b8e4933 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e4931 X0
               have i₂ := b8e4464 (τ X0)
               grind)
            | exact superpose b8e4464 b8e4931
            | (have j0 := b8e4931 X0
               grind)
            | exact resolve b8e4931 b8e4464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4931
          have b8e4955 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e4933 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e4933
            | (have j0 := b8e4933 X0
               grind)
            | exact resolve b8e4933 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4933
          have b8e4972 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b8e4955 X0
               have i₂ := b8e4464 (τ X0)
               grind)
            | exact superpose b8e4464 b8e4955
            | (have j0 := b8e4955 X0
               grind)
            | exact resolve b8e4955 b8e4464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4464 b8e4955
          have b8e5062 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 x X0
               have i₂ := b8e4875 X0
               grind)
            | exact superpose b8e4875 b8e13
            | exact resolve b8e13 b8e4875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e5151 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e5062 X0 X1
               have i₂ := b8e4875 X1
               grind)
            | exact superpose b8e4875 b8e5062
            | exact resolve b8e5062 b8e4875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4875 b8e5062
          have b8e8772 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e48 X0 (σ x)
               have i₂ := b8e4972 (σ X0)
               grind)
            | exact superpose b8e4972 b8e48
            | (have j1 := b8e4972 (σ X0)
               grind)
            | exact resolve b8e48 b8e4972
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48 b8e4972
          have b8e8794 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e8772 X0
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e8772
            | (have j0 := b8e8772 X0
               grind)
            | exact resolve b8e8772 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8772
          have b8e8813 : ∀ X0 : G, (k X0 x) = X0 ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e8794 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e8794
            | (have j0 := b8e8794 X0
               grind)
            | exact resolve b8e8794 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8794
          have b8e8824 : ∀ X0 : G, (k X0 x) = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e8813 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e8813
            | (have j0 := b8e8813 X0
               grind)
            | exact resolve b8e8813 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8813
          have b8e9051 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e130
               have i₂ := b8e8824 y
               grind)
            | exact superpose b8e8824 b8e130
            | (have j1 := b8e8824 y
               grind)
            | exact resolve b8e130 b8e8824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130 b8e8824
          have b8e9056 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e9051
               have r₂ := b8e21
               grind)
            | exact resolve b8e9051 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9051
          have b8e9067 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e9056
               have i₂ := b8e2011
               grind)
            | exact superpose b8e2011 b8e9056
            | exact resolve b8e9056 b8e2011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2011 b8e9056
          have b8e9068 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e9067
          have b8e9341 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ (M.op x x))) X0) (σ y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e88 x (σ y) X0
               have i₂ := b8e9068
               grind)
            | exact superpose b8e9068 b8e88
            | exact resolve b8e88 b8e9068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e9348 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e13 (σ y) (σ x) X0
               have i₂ := b8e9068
               grind)
            | exact superpose b8e9068 b8e13
            | exact resolve b8e13 b8e9068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9068
          have b8e9392 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e9348 X0
               have i₂ := b8e398 (σ x) X0
               grind)
            | exact superpose b8e398 b8e9348
            | exact resolve b8e9348 b8e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e398 b8e9348
          have b8e9393 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x x)) X0) (σ y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e9341 X0
               have i₂ := b8e399 x
               grind)
            | exact superpose b8e399 b8e9341
            | exact resolve b8e9341 b8e399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399 b8e9341
          have b8e9402 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e9393 X0
               have i₂ := b8e4287
               grind)
            | exact superpose b8e4287 b8e9393
            | exact resolve b8e9393 b8e4287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4287 b8e9393
          have b8e9405 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e9402 X0
               have i₂ := b8e9392 X0
               grind)
            | exact superpose b8e9392 b8e9402
            | exact resolve b8e9402 b8e9392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9392 b8e9402
          have b8e9608 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
            first
            | (have i₁ := b8e447 (σ y)
               have i₂ := b8e9405 (σ y)
               grind)
            | exact superpose b8e9405 b8e447
            | exact resolve b8e447 b8e9405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e447
          have b8e9648 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e5151 X0 (σ y)
               have i₂ := b8e9405 X0
               grind)
            | exact superpose b8e9405 b8e5151
            | exact resolve b8e5151 b8e9405
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9405
          have b8e9702 : (τ (σ y)) = (τ (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b8e9608
               have i₂ := b8e148 (σ y)
               grind)
            | exact superpose b8e148 b8e9608
            | exact resolve b8e9608 b8e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148 b8e9608
          have b8e9719 : (τ (σ y)) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b8e9702
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e9702
            | exact resolve b8e9702 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e9702
          have b8e9724 : (τ (σ y)) = (M.op y y) := by
            first
            | (have i₁ := b8e9719
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e9719
            | exact resolve b8e9719 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9719
          have b8e9726 : y = (M.op y y) := by
            first
            | (have i₁ := b8e9724
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e9724
            | exact resolve b8e9724 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9724
          have b8e9919 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e13 X0 y y
               have i₂ := b8e9726
               grind)
            | exact superpose b8e9726 b8e13
            | exact resolve b8e13 b8e9726
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9726
          have b8e9957 : ∀ X0 : G, (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e9919 X0
               have i₂ := b8e5151 X0 y
               grind)
            | exact superpose b8e5151 b8e9919
            | exact resolve b8e9919 b8e5151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9919
          have b8e10223 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b8e5151 X0 y
               have i₂ := b8e9957 X0
               grind)
            | exact superpose b8e9957 b8e5151
            | exact resolve b8e5151 b8e9957
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5151 b8e9957
          have b8e11764 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e9648 (σ x)
               grind)
            | exact superpose b8e9648 b8e20
            | exact resolve b8e20 b8e9648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9648
          have b8e11808 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e11764
               have i₂ := b8e10223 x
               grind)
            | exact superpose b8e10223 b8e11764
            | exact resolve b8e11764 b8e10223
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10223 b8e11764
          have b8e11809 : False := by grind
          exact b8e11809
