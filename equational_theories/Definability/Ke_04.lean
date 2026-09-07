import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_x_pxy_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e67 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e35 X0 X1
             have i₂ := b1e17 (τ X0) X1
             grind)
          | exact superpose b1e17 b1e35
          | (have j1 := b1e17 (τ X0) X1
             grind)
          | exact resolve b1e35 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e159 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (σ X0) (σ X1)
             have i₂ := b1e56 X0 X1
             grind)
          | exact superpose b1e56 b1e16
          | (have j0 := b1e16 (σ X0) (σ X1)
             have j1 := b1e56 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X0) (σ X1)
             have r₂ := b1e56 X0 X1
             grind)
          | (have r₁ := b1e16 (σ X1) (σ X0)
             have r₂ := b1e56 X0 X1
             grind)
          | exact resolve b1e16 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e167 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e159 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e159
        have b1e168 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e167 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e167
        have b1e177 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e168 X0 X1
             have j1 := b1e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b1e168 X0 X1
             have r₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact resolve b1e168 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e168
        have b1e190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e177 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e177
          | (have j0 := b1e177 X0 X1
             grind)
          | exact resolve b1e177 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e177
        have b1e697 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 x)) ∨ (σ X0) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e25 (σ X0)
             have i₂ := b1e190 X0 x
             grind)
          | exact superpose b1e190 b1e25
          | (have j1 := b1e190 X0 x
             grind)
          | exact resolve b1e25 b1e190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e190
        have b1e892 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e67 (σ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e67
          | exact resolve b1e67 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e932 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e892 X0 X1
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e892
          | (have j0 := b1e892 X0 X1
             grind)
          | exact resolve b1e892 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e892
        have b1e4956 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e697 x
             grind)
          | exact superpose b1e697 b1e21
          | (have j1 := b1e697 x
             grind)
          | exact resolve b1e21 b1e697
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e697
        have b1e6251 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e4956
             have i₂ := b1e932 x x
             grind)
          | exact superpose b1e932 b1e4956
          | (have j1 := b1e932 x x
             grind)
          | exact resolve b1e4956 b1e932
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e932 b1e4956
        have b1e6252 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e6251
        have b1e6254 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e6252
             have i₂ := b1e24 x
             grind)
          | exact superpose b1e24 b1e6252
          | exact resolve b1e6252 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6252
        have b1e6257 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e6254
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e6254
          | exact resolve b1e6254 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6254
        have b1e6258 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e6257
        have b1e6263 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e6258
             have i₂ := b1e24 x
             grind)
          | exact superpose b1e24 b1e6258
          | exact resolve b1e6258 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6258
        have b1e6266 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e6263
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e6263
          | exact resolve b1e6263 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6263
        have b1e6269 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e6266
             have i₂ := b1e24 x
             grind)
          | exact superpose b1e24 b1e6266
          | exact resolve b1e6266 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e6266
        have b1e6271 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e6269
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e6269
          | exact resolve b1e6269 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6269
        have b1e6570 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e6271
             grind)
          | exact superpose b1e6271 b1e13
          | exact resolve b1e13 b1e6271
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6271
        have b1e6651 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e6570
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e6570
          | exact resolve b1e6570 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6570
        have b1e6652 : x = y := by grind
        clear b1e6651
        have b1e6945 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e6652
             grind)
          | exact superpose b1e6652 b1e21
          | exact resolve b1e21 b1e6652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6946 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e6652
             grind)
          | exact superpose b1e6652 b1e22
          | exact resolve b1e22 b1e6652
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6652
        have b1e6985 : False := by grind
        exact b1e6985
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b2e24 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
        have b2e28 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X1 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 X0)
             have r₂ := b2e12 X0 X0 X0
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e31 X0 X1
             grind)
          | exact superpose b2e31 b2e13
          | exact resolve b2e13 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
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
        have b2e38 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op (M.op X1 X2) X0) = X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e16 (M.op X1 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e16
          | (have j0 := b2e16 (M.op X1 X2) X0
             grind)
          | (have r₁ := b2e16 (M.op X0 X0) X0
             have r₂ := b2e12 X0 X0 X0
             grind)
          | exact resolve b2e16 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : x = (M.op y x) ∨ y = (k y x) := by grind
        clear b2e37
        have b2e42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e38 X0 X1 X2
             have j1 := b2e15 (M.op X1 X2) X0
             grind)
          | (have r₁ := b2e38 X1 X1 X2
             have r₂ := b2e15 (M.op X1 X2) X1
             grind)
          | exact resolve b2e38 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e43 : y = (k y x) := by
          first
          | (have j1 := b2e15 y x
             grind)
          | (have r₁ := b2e40
             have r₂ := b2e15 y x
             grind)
          | exact resolve b2e40 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e57 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e32 X1 X0
             grind)
          | exact superpose b2e32 b2e13
          | exact resolve b2e13 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e28 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e81 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e42 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e112 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e47 y x
             grind)
          | exact superpose b2e47 b2e21
          | (have j1 := b2e47 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e47 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e47 x y
             grind)
          | exact resolve b2e21 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e113 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op X1 (σ X2)) = (M.op X1 (σ X0)) ∨ (σ X2) = (M.op (σ X0) (σ X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 (σ X2) (σ X0)
             have i₂ := b2e47 X0 X2
             grind)
          | exact superpose b2e47 b2e12
          | (have j1 := b2e47 X0 X2
             grind)
          | exact resolve b2e12 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e115 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 (σ X0) (σ X1)
             have i₂ := b2e47 X0 X1
             grind)
          | exact superpose b2e47 b2e16
          | (have j0 := b2e16 (σ X0) (σ X1)
             have j1 := b2e47 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X0) (σ X1)
             have r₂ := b2e47 X0 X1
             grind)
          | (have r₁ := b2e16 (σ X1) (σ X0)
             have r₂ := b2e47 X0 X1
             grind)
          | exact resolve b2e16 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e120 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e47 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e122 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e120 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e120
        have b2e123 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e115 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115
        have b2e124 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e123 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123
        have b2e126 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e112
        have b2e131 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e124 X0 X1
             have j1 := b2e15 (σ X0) (σ X1)
             grind)
          | (have r₁ := b2e124 X0 X1
             have r₂ := b2e15 (σ X0) (σ X1)
             grind)
          | exact resolve b2e124 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124
        have b2e133 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e126
             have r₂ := b2e22
             grind)
          | exact resolve b2e126 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126
        have b2e140 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e131 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e131
          | (have j0 := b2e131 X0 X1
             grind)
          | exact resolve b2e131 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e131
        have b2e141 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e133
             have i₂ := b2e43
             grind)
          | exact superpose b2e43 b2e133
          | exact resolve b2e133 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e133
        have b2e142 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e141
             grind)
          | exact superpose b2e141 b2e22
          | exact resolve b2e22 b2e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e141
        have b2e152 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e36 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e36
          | exact resolve b2e36 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e156 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b2e36 (M.op (σ X0) (σ X0)) X0
             have i₂ := b2e81 (σ X0)
             grind)
          | exact superpose b2e81 b2e36
          | exact resolve b2e36 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e81
        have b2e168 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e57 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e66 (σ X0)
             grind)
          | exact superpose b2e66 b2e57
          | exact resolve b2e57 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e176 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e168 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e168
          | exact resolve b2e168 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e168
        have b2e476 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e122 (τ X0)
             have i₂ := b2e32 X0 (τ X0)
             grind)
          | exact superpose b2e32 b2e122
          | (have j0 := b2e122 (τ X0)
             grind)
          | exact resolve b2e122 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e122
        have b2e478 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e476 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e476
          | (have j0 := b2e476 X0
             grind)
          | exact resolve b2e476 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e476
        have b2e481 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e478 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e478
          | (have j0 := b2e478 X0
             grind)
          | exact resolve b2e478 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478
        have b2e500 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e140 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e140
          | exact resolve b2e140 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e517 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (σ X0) (σ X1)
             have i₂ := b2e140 X0 X1
             grind)
          | exact superpose b2e140 b2e12
          | (have j1 := b2e140 X0 X1
             grind)
          | exact resolve b2e12 b2e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e538 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e500 X0 X1
             have i₂ := b2e31 X0 X1
             grind)
          | exact superpose b2e31 b2e500
          | (have j0 := b2e500 X0 X1
             grind)
          | exact resolve b2e500 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e500
        have b2e542 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e538 X0 X1
             have i₂ := b2e31 X0 X1
             grind)
          | exact superpose b2e31 b2e538
          | (have j0 := b2e538 X0 X1
             grind)
          | exact resolve b2e538 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e538
        have b2e986 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X2)) ∨ (M.op (σ X2) (σ X1)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X2) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e113 X2 (σ X0) X1
             have i₂ := b2e47 X0 X1
             grind)
          | exact superpose b2e47 b2e113
          | (have j0 := b2e113 X2 X1 X1
             have j1 := b2e47 X2 X1
             grind)
          | exact resolve b2e113 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113
        have b2e2141 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e156 x
             have i₂ := b2e140 x x
             grind)
          | exact superpose b2e140 b2e156
          | (have j1 := b2e140 X0 X0
             grind)
          | exact resolve b2e156 b2e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e140
        have b2e2142 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e156 x
             have i₂ := b2e47 x x
             grind)
          | exact superpose b2e47 b2e156
          | (have j1 := b2e47 X0 X0
             grind)
          | exact resolve b2e156 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e156
        have b2e2166 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e2142 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2142
        have b2e2181 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e2166 X0
             have i₂ := b2e13 (k X0 X0)
             grind)
          | exact superpose b2e13 b2e2166
          | (have j0 := b2e2166 X0
             grind)
          | exact resolve b2e2166 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2166
        have b2e2182 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e2141 X0
             have i₂ := b2e13 (k X0 X0)
             grind)
          | exact superpose b2e13 b2e2141
          | (have j0 := b2e2141 X0
             grind)
          | exact resolve b2e2141 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2141
        have b2e2969 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e542 X0 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e542
          | exact resolve b2e542 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e542
        have b2e3139 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (k (σ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e57 X0 X1
             have i₂ := b2e2969 X1 (σ X0)
             grind)
          | exact superpose b2e2969 b2e57
          | (have j1 := b2e2969 X1 (σ X0)
             grind)
          | exact resolve b2e57 b2e2969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e2969
        have b2e10148 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (σ (τ X0)) = (σ (τ (k X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e2182 (τ X0)
             have i₂ := b2e152 X0 X0
             grind)
          | exact superpose b2e152 b2e2182
          | exact resolve b2e2182 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2182
        have b2e10234 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (σ (τ X0)) = (σ (τ (k X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e10148 X0
             have i₂ := b2e152 X0 (k X0 X0)
             grind)
          | exact superpose b2e152 b2e10148
          | (have j0 := b2e10148 X0
             grind)
          | exact resolve b2e10148 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10148
        have b2e10272 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) := by
          intro X0
          first
          | (have i₁ := b2e10234 X0
             have i₂ := b2e14 (k X0 X0)
             grind)
          | exact superpose b2e14 b2e10234
          | (have j0 := b2e10234 X0
             grind)
          | exact resolve b2e10234 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10234
        have b2e10307 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e10272 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e10272
          | (have j0 := b2e10272 X0
             grind)
          | exact resolve b2e10272 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10272
        have b2e19865 : ∀ X0 : G, (τ (k X0 X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e2181 (τ X0)
             have i₂ := b2e152 X0 X0
             grind)
          | exact superpose b2e152 b2e2181
          | (have j0 := b2e2181 (τ X0)
             grind)
          | exact resolve b2e2181 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2181
        have b2e19969 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e19865 X0
             have i₂ := b2e152 X0 (k X0 X0)
             grind)
          | exact superpose b2e152 b2e19865
          | (have j0 := b2e19865 X0
             grind)
          | exact resolve b2e19865 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19865
        have b2e20011 : ∀ X0 : G, (τ (k X0 X0)) = (τ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e19969 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e19969
          | (have j0 := b2e19969 X0
             grind)
          | exact resolve b2e19969 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e19969
        have b2e26150 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) y)) ∨ (σ X0) = (k (σ X0) x) := by
          intro X0
          first
          | (have i₁ := b2e3139 X0 x
             have i₂ := b2e24 (σ X0)
             grind)
          | exact superpose b2e24 b2e3139
          | (have j0 := b2e3139 X0 x
             grind)
          | exact resolve b2e3139 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3139
        have b2e28919 : ∀ X0 : G, (τ (M.op X0 y)) = (k (τ X0) (τ x)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e26150 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e26150
          | exact resolve b2e26150 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26150
        have b2e29034 : ∀ X0 : G, (τ (M.op X0 y)) = (τ (k X0 x)) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e28919 X0
             have i₂ := b2e152 x X0
             grind)
          | exact superpose b2e152 b2e28919
          | (have j0 := b2e28919 X0
             grind)
          | exact resolve b2e28919 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28919
        have b2e29262 : ∀ X0 X1 : G, (k (τ (M.op X0 y)) (τ X1)) = (τ (k (k X0 x) X1)) ∨ (k X0 x) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e152 X1 (k X0 x)
             have i₂ := b2e29034 X0
             grind)
          | exact superpose b2e29034 b2e152
          | (have j1 := b2e29034 X0
             grind)
          | exact resolve b2e152 b2e29034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29034
        have b2e29341 : ∀ X0 X1 : G, (τ (k (M.op X0 y) X1)) = (τ (k (k X0 x) X1)) ∨ (k X0 x) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e29262 X0 X1
             have i₂ := b2e152 X1 (M.op X0 y)
             grind)
          | exact superpose b2e152 b2e29262
          | (have j0 := b2e29262 X0 X1
             grind)
          | exact resolve b2e29262 b2e152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e152 b2e29262
        have b2e105208 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e986 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e986
        have b2e105218 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e105208 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105208
        have b2e105219 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e105218 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105218
        have b2e262245 : (τ (k x x)) = (τ (k (M.op x y) x)) ∨ x = (M.op x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e20011 x
             have i₂ := b2e29341 x x
             grind)
          | exact superpose b2e29341 b2e20011
          | (have j0 := b2e20011 x
             have j1 := b2e29341 x x
             grind)
          | exact resolve b2e20011 b2e29341
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20011
        have b2e262246 : (τ (k x x)) = (τ (k (M.op x y) x)) ∨ x = (k x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e10307 x
             have i₂ := b2e29341 x x
             grind)
          | exact superpose b2e29341 b2e10307
          | (have j0 := b2e10307 x
             have j1 := b2e29341 x x
             grind)
          | exact resolve b2e10307 b2e29341
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e10307 b2e29341
        have b2e262269 : (τ (k x x)) = (τ (k (M.op x y) x)) ∨ x = (k x x) := by grind
        clear b2e262246
        have b2e262288 : (τ (k y x)) = (τ (k x x)) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e262269
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e262269
          | exact resolve b2e262269 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262269
        have b2e262289 : (τ (k x x)) = (τ (k (M.op x y) x)) ∨ x = (M.op x x) := by
          first
          | (have j1 := b2e481 x
             grind)
          | (have r₁ := b2e262245
             have r₂ := b2e481 x
             grind)
          | exact resolve b2e262245 b2e481
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e481 b2e262245
        have b2e262314 : (τ y) = (τ (k x x)) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e262288
             have i₂ := b2e43
             grind)
          | exact superpose b2e43 b2e262288
          | exact resolve b2e262288 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262288
        have b2e262315 : (τ (k y x)) = (τ (k x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e262289
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e262289
          | exact resolve b2e262289 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262289
        have b2e262334 : (τ y) = (τ (k x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e262315
             have i₂ := b2e43
             grind)
          | exact superpose b2e43 b2e262315
          | exact resolve b2e262315 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43 b2e262315
        have b2e262337 : x = (M.op x y) ∨ (τ y) = (τ (k x x)) := by
          first
          | (have i₁ := b2e262334
             have i₂ := b2e24 x
             grind)
          | exact superpose b2e24 b2e262334
          | exact resolve b2e262334 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e262334
        have b2e262338 : (τ y) = (τ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e262337
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e262337
          | exact resolve b2e262337 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262337
        have b2e264362 : (k x x) = (σ (τ y)) ∨ x = y := by
          first
          | (have i₁ := b2e14 (k x x)
             have i₂ := b2e262338
             grind)
          | exact superpose b2e262338 b2e14
          | exact resolve b2e14 b2e262338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262338
        have b2e264465 : y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e264362
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e264362
          | exact resolve b2e264362 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e264362
        have b2e266267 : (k x x) = (σ (τ y)) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e14 (k x x)
             have i₂ := b2e262314
             grind)
          | exact superpose b2e262314 b2e14
          | exact resolve b2e14 b2e262314
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e262314
        have b2e266321 : x = (k x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b2e266267
             have i₂ := b2e14 y
             grind)
          | exact superpose b2e14 b2e266267
          | exact resolve b2e266267 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e266267
        have b2e267131 : x ≠ y ∨ y = (k x x) := by grind
        clear b2e266321
        have b2e267148 : y = (k x x) := by
          first
          | (have r₁ := b2e267131
             have r₂ := b2e264465
             grind)
          | exact resolve b2e267131 b2e264465
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e264465 b2e267131
        have b2e268086 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e517 x x x
             have i₂ := b2e267148
             grind)
          | exact superpose b2e267148 b2e517
          | exact resolve b2e517 b2e267148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e517
        have b2e268154 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b2e268086 X0
             grind)
          | (have r₁ := b2e268086 X0
             have r₂ := b2e142
             grind)
          | exact resolve b2e268086 b2e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e268086
        have b2e272494 : x = (k x (τ (M.op (σ x) (σ y)))) := by
          first
          | (have i₁ := b2e176 x
             have i₂ := b2e268154 (σ x)
             grind)
          | exact superpose b2e268154 b2e176
          | exact resolve b2e176 b2e268154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e176
        have b2e272495 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e105219 x
             have i₂ := b2e268154 (σ x)
             grind)
          | exact superpose b2e268154 b2e105219
          | exact resolve b2e105219 b2e268154
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105219 b2e268154
        have b2e272626 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e272495
             have i₂ := b2e267148
             grind)
          | exact superpose b2e267148 b2e272495
          | exact resolve b2e272495 b2e267148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e272495
        have b2e272633 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e272626
             have r₂ := b2e21
             grind)
          | exact resolve b2e272626 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e272626
        have b2e277716 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b2e272494
             have i₂ := b2e272633
             grind)
          | exact superpose b2e272633 b2e272494
          | exact resolve b2e272494 b2e272633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e272494 b2e272633
        have b2e277760 : x = (k x x) := by
          first
          | (have i₁ := b2e277716
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e277716
          | exact resolve b2e277716 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277716
        have b2e277769 : x = y := by
          first
          | (have i₁ := b2e277760
             have i₂ := b2e267148
             grind)
          | exact superpose b2e267148 b2e277760
          | exact resolve b2e277760 b2e267148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e267148 b2e277760
        have b2e278221 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e142
             have i₂ := b2e277769
             grind)
          | exact superpose b2e277769 b2e142
          | exact resolve b2e142 b2e277769
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e142 b2e277769
        have b2e278362 : False := by grind
        exact b2e278362
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
        have b3e24 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e15 X0 x
             have i₂ := b3e24 X0
             grind)
          | exact superpose b3e24 b3e15
          | (have j0 := b3e15 X0 x
             grind)
          | exact resolve b3e15 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e140 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e53 X0 x
             have i₂ := b3e25 (σ X0)
             grind)
          | exact superpose b3e25 b3e53
          | (have j0 := b3e53 X0 x
             grind)
          | exact resolve b3e53 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e1208 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e25 (σ x)
             have i₂ := b3e140 x
             grind)
          | exact superpose b3e140 b3e25
          | (have j1 := b3e140 x
             grind)
          | exact resolve b3e25 b3e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e140
        have b3e1230 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by grind
        clear b3e1208
        have b3e1245 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e1230
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1230
          | exact resolve b3e1230 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1230
        have b3e1263 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1245
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1245
          | exact resolve b3e1245 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1245
        have b3e1272 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1263
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e1263
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e1263 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1305 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e1272
        have b3e1319 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1305
             have i₂ := b3e24 x
             grind)
          | exact superpose b3e24 b3e1305
          | exact resolve b3e1305 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1305
        have b3e1320 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b3e1319
             have r₂ := b3e23
             grind)
          | exact resolve b3e1319 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e1319
        have b3e1321 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1320
             have i₂ := b3e24 x
             grind)
          | exact superpose b3e24 b3e1320
          | exact resolve b3e1320 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e1320
        have b3e1515 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e36 x
             have i₂ := b3e1321
             grind)
          | exact superpose b3e1321 b3e36
          | (have j0 := b3e36 x
             grind)
          | (have r₁ := b3e36 x
             have r₂ := b3e1321
             grind)
          | exact resolve b3e36 b3e1321
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e1321
        have b3e1525 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e1515
        have b3e1784 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1263
             have i₂ := b3e1525
             grind)
          | exact superpose b3e1525 b3e1263
          | exact resolve b3e1263 b3e1525
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1263 b3e1525
        have b3e1794 : (σ x) = (σ y) := by grind
        clear b3e1784
        have b3e1867 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e1794
             grind)
          | exact superpose b3e1794 b3e13
          | exact resolve b3e13 b3e1794
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1794
        have b3e1919 : x = y := by
          first
          | (have i₁ := b3e1867
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e1867
          | exact resolve b3e1867 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1867
        have b3e2027 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e1919
             grind)
          | exact superpose b3e1919 b3e20
          | exact resolve b3e20 b3e1919
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2028 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1919
             grind)
          | exact superpose b3e1919 b3e21
          | exact resolve b3e21 b3e1919
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1919
        have b3e2048 : False := by grind
        exact b3e2048
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
          have b4e26 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
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
          have b4e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e26 (σ x)
               grind)
            | exact superpose b4e26 b4e20
            | exact resolve b4e20 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e61 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e59
               have i₂ := b4e25 x
               grind)
            | exact superpose b4e25 b4e59
            | exact resolve b4e59 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e59
          have b4e143 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) (σ X1)
               have i₂ := b4e53 X0 X1
               grind)
            | exact superpose b4e53 b4e17
            | (have j0 := b4e17 (σ X0) (σ X1)
               have j1 := b4e53 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X0) (σ X1)
               have r₂ := b4e53 X0 X1
               grind)
            | (have r₁ := b4e17 (σ X1) (σ X0)
               have r₂ := b4e53 X0 X1
               grind)
            | exact resolve b4e17 b4e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e149 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e151 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e143
          have b4e152 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e151 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e151
          have b4e158 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e152 X0 X1
               have j1 := b4e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b4e152 X0 X1
               have r₂ := b4e16 (σ X0) (σ X1)
               grind)
            | exact resolve b4e152 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e152
          have b4e167 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e158 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e158
            | (have j0 := b4e158 X0 X1
               grind)
            | exact resolve b4e158 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e158
          have b4e620 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e167 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e167
            | exact resolve b4e167 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e634 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e61
               have i₂ := b4e167 x x
               grind)
            | exact superpose b4e167 b4e61
            | (have j1 := b4e167 x x
               grind)
            | exact resolve b4e61 b4e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e167
          have b4e670 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e620 X0 X1
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e620
            | (have j0 := b4e620 X0 X1
               grind)
            | exact resolve b4e620 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e620
          have b4e675 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e670 X0 X1
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e670
            | (have j0 := b4e670 X0 X1
               grind)
            | exact resolve b4e670 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e670
          have b4e2869 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e675 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e675
            | exact resolve b4e675 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e675
          have b4e3213 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e2869 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2869
          have b4e3942 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e634
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e634
            | (have j1 := b4e18 x x
               grind)
            | exact resolve b4e634 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e634
          have b4e3943 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e3942
          have b4e3944 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b4e3943
          have b4e4101 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e3944
               grind)
            | exact superpose b4e3944 b4e14
            | exact resolve b4e14 b4e3944
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3944
          have b4e4167 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e4101
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e4101
            | exact resolve b4e4101 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4101
          have b4e4168 : x = (M.op x x) := by grind
          clear b4e4167
          have b4e4267 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b4e3213 x x
               have i₂ := b4e4168
               grind)
            | exact superpose b4e4168 b4e3213
            | (have j0 := b4e3213 x x
               grind)
            | (have r₁ := b4e3213 x x
               have r₂ := b4e4168
               grind)
            | exact resolve b4e3213 b4e4168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3213
          have b4e4270 : x = (k x x) := by grind
          clear b4e4267
          have b4e4437 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e149 x x
               have i₂ := b4e4270
               grind)
            | exact superpose b4e4270 b4e149
            | (have j0 := b4e149 x x
               grind)
            | exact resolve b4e149 b4e4270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149 b4e4270
          have b4e4438 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e4437
          have b4e4439 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e4438
          have b4e4598 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e61
               have i₂ := b4e4439
               grind)
            | exact superpose b4e4439 b4e61
            | exact resolve b4e61 b4e4439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61 b4e4439
          have b4e4669 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e4598
               have i₂ := b4e4168
               grind)
            | exact superpose b4e4168 b4e4598
            | exact resolve b4e4598 b4e4168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4168 b4e4598
          have b4e4670 : False := by grind
          exact b4e4670
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
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
          have b5e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e35 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) := by
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
          have b5e38 : y = (M.op x y) ∨ x = (k x y) := by grind
          clear b5e35
          have b5e41 : x = (k x y) := by
            first
            | (have r₁ := b5e38
               have r₂ := b5e21
               grind)
            | exact resolve b5e38 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e14
            | exact resolve b5e14 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e59 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e31 X1 X0
               grind)
            | exact superpose b5e31 b5e14
            | exact resolve b5e14 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e108 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e45 x y
               grind)
            | exact superpose b5e45 b5e24
            | (have j1 := b5e45 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e45 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e45 y x
               grind)
            | exact resolve b5e24 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e111 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e45 X0 X1
               grind)
            | exact superpose b5e45 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e45 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e45 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X0)
               have r₂ := b5e45 X0 X1
               grind)
            | exact resolve b5e17 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e117 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e45 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e119 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e111 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111
          have b5e120 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e119 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e119
          have b5e122 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e108
          have b5e126 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e120 X0 X1
               have j1 := b5e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b5e120 X0 X1
               have r₂ := b5e16 (σ X0) (σ X1)
               grind)
            | exact resolve b5e120 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e128 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e122
               have r₂ := b5e23
               grind)
            | exact resolve b5e122 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122
          have b5e134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e126 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e126
            | (have j0 := b5e126 X0 X1
               grind)
            | exact resolve b5e126 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e126
          have b5e135 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e128
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e128
            | exact resolve b5e128 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e128
          have b5e136 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e135
               grind)
            | exact superpose b5e135 b5e20
            | exact resolve b5e20 b5e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e137 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e135
               grind)
            | exact superpose b5e135 b5e23
            | exact resolve b5e23 b5e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e146 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e136
               have i₂ := b5e25 x
               grind)
            | exact superpose b5e25 b5e136
            | exact resolve b5e136 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e136
          have b5e157 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e52 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e52
            | exact resolve b5e52 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e504 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e134 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e134
            | exact resolve b5e134 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e544 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e504 X0 X1
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e504
            | (have j0 := b5e504 X0 X1
               grind)
            | exact resolve b5e504 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e504
          have b5e549 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e544 X0 X1
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e544
            | (have j0 := b5e544 X0 X1
               grind)
            | exact resolve b5e544 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e544
          have b5e728 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e117 (τ X0) (τ X1)
               have i₂ := b5e157 X1 X0
               grind)
            | exact superpose b5e157 b5e117
            | (have j0 := b5e117 (τ X0) (τ X1)
               grind)
            | exact resolve b5e117 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e117
          have b5e737 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e728 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e728
            | (have j0 := b5e728 X0 X1
               grind)
            | exact resolve b5e728 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e728
          have b5e742 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e737 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e737
            | (have j0 := b5e737 X0 X1
               grind)
            | exact resolve b5e737 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e737
          have b5e746 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e742 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e742
            | (have j0 := b5e742 X0 X1
               grind)
            | exact resolve b5e742 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e742
          have b5e749 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e746 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e746
            | (have j0 := b5e746 X0 X1
               grind)
            | exact resolve b5e746 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e746
          have b5e750 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e749 X0 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e749
            | (have j0 := b5e749 X0 X1
               grind)
            | exact resolve b5e749 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e749
          have b5e751 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e750 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e750
            | (have j0 := b5e750 X0 X1
               grind)
            | exact resolve b5e750 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e750
          have b5e2986 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e549 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e549
            | exact resolve b5e549 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e549
          have b5e3156 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e59 X0 X1
               have i₂ := b5e2986 X1 (σ X0)
               grind)
            | exact superpose b5e2986 b5e59
            | (have j1 := b5e2986 X1 (σ X0)
               grind)
            | exact resolve b5e59 b5e2986
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3173 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e2986 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2986
          have b5e3334 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e3173 X0 (M.op X1 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e3173
            | (have j0 := b5e3173 X0 X1
               grind)
            | exact resolve b5e3173 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3173
          have b5e3735 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e3334 (σ x) (σ y) X0
               have i₂ := b5e135
               grind)
            | exact superpose b5e135 b5e3334
            | (have j0 := b5e3334 (σ x) (σ y) X0
               grind)
            | (have r₁ := b5e3334 (σ x) (σ y) x
               have r₂ := b5e135
               grind)
            | exact resolve b5e3334 b5e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e135 b5e3334
          have b5e3736 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have j0 := b5e3735 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3735
          have b5e3991 : ∀ X0 : G, (k x (τ (M.op (σ y) X0))) = (τ (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e59 x (M.op (σ y) X0)
               have i₂ := b5e3736 X0
               grind)
            | exact superpose b5e3736 b5e59
            | exact resolve b5e59 b5e3736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e3736
          have b5e4003 : ∀ X0 : G, x = (k x (τ (M.op (σ y) X0))) := by
            intro X0
            first
            | (have i₁ := b5e3991 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e3991
            | exact resolve b5e3991 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3991
          have b5e4026 : ∀ X0 : G, x = (k x (τ (σ (k y X0)))) ∨ (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b5e4003 (σ X0)
               have i₂ := b5e134 y X0
               grind)
            | exact superpose b5e134 b5e4003
            | (have j1 := b5e134 y X0
               grind)
            | exact resolve b5e4003 b5e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e134 b5e4003
          have b5e4053 : ∀ X0 : G, x = (k x (k y X0)) ∨ (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b5e4026 X0
               have i₂ := b5e14 (k y X0)
               grind)
            | exact superpose b5e14 b5e4026
            | (have j0 := b5e4026 X0
               grind)
            | exact resolve b5e4026 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4026
          have b5e26177 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op (σ X0) x)) ∨ (σ X0) = (k (σ X0) y) := by
            intro X0
            first
            | (have i₁ := b5e3156 X0 y
               have i₂ := b5e25 (σ X0)
               grind)
            | exact superpose b5e25 b5e3156
            | (have j0 := b5e3156 X0 y
               grind)
            | exact resolve b5e3156 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3156
          have b5e28972 : ∀ X0 : G, (τ (M.op X0 x)) = (k (τ X0) (τ y)) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e26177 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e26177
            | exact resolve b5e26177 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26177
          have b5e29087 : ∀ X0 : G, (τ (M.op X0 x)) = (τ (k X0 y)) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e28972 X0
               have i₂ := b5e157 y X0
               grind)
            | exact superpose b5e157 b5e28972
            | (have j0 := b5e28972 X0
               grind)
            | exact resolve b5e28972 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e157 b5e28972
          have b5e29160 : ∀ X0 : G, (k X0 y) = (σ (τ (M.op X0 x))) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e15 (k X0 y)
               have i₂ := b5e29087 X0
               grind)
            | exact superpose b5e29087 b5e15
            | (have j1 := b5e29087 X0
               grind)
            | exact resolve b5e15 b5e29087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29087
          have b5e29255 : ∀ X0 : G, (M.op X0 x) = (k X0 y) ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29160 X0
               have i₂ := b5e15 (M.op X0 x)
               grind)
            | exact superpose b5e15 b5e29160
            | (have j0 := b5e29160 X0
               grind)
            | exact resolve b5e29160 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29160
          have b5e29583 : x = (k x (M.op y x)) ∨ (σ y) = (σ (M.op y x)) ∨ y = (k y y) := by
            first
            | (have i₁ := b5e4053 y
               have i₂ := b5e29255 y
               grind)
            | exact superpose b5e29255 b5e4053
            | (have j1 := b5e29255 y
               grind)
            | exact resolve b5e4053 b5e29255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4053 b5e29255
          have b5e29585 : x = (k x x) ∨ (σ y) = (σ (M.op y x)) ∨ y = (k y y) := by
            first
            | (have i₁ := b5e29583
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e29583
            | exact resolve b5e29583 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29583
          have b5e29629 : (σ x) = (σ y) ∨ x = (k x x) ∨ y = (k y y) := by
            first
            | (have i₁ := b5e29585
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e29585
            | exact resolve b5e29585 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29585
          have b5e29651 : y = (k y y) ∨ x = (k x x) := by
            first
            | (have r₁ := b5e29629
               have r₂ := b5e137
               grind)
            | exact resolve b5e29629 b5e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29629
          have b5e30012 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e751 y y
               have i₂ := b5e29651
               grind)
            | exact superpose b5e29651 b5e751
            | (have j0 := b5e751 y y
               grind)
            | (have r₁ := b5e751 y y
               have r₂ := b5e29651
               grind)
            | (have r₁ := b5e751 x x
               have r₂ := b5e29651
               grind)
            | exact resolve b5e751 b5e29651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29651
          have b5e30013 : y ≠ y ∨ y = (M.op y y) ∨ x = (k x x) := by grind
          clear b5e30012
          have b5e30014 : y = (M.op y y) ∨ x = (k x x) := by grind
          clear b5e30013
          have b5e30029 : y = (M.op y x) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e30014
               have i₂ := b5e25 y
               grind)
            | exact superpose b5e25 b5e30014
            | exact resolve b5e30014 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e30014
          have b5e30043 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e30029
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e30029
            | exact resolve b5e30029 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30029
          have b5e30248 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e751 x x
               have i₂ := b5e30043
               grind)
            | exact superpose b5e30043 b5e751
            | (have j0 := b5e751 x x
               grind)
            | (have r₁ := b5e751 x x
               have r₂ := b5e30043
               grind)
            | exact resolve b5e751 b5e30043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e751 b5e30043
          have b5e30249 : x ≠ x ∨ x = (M.op x x) ∨ x = y := by grind
          clear b5e30248
          have b5e30250 : x = (M.op x x) ∨ x = y := by grind
          clear b5e30249
          have b5e30543 : (σ x) ≠ (σ x) ∨ x = y := by
            first
            | (have i₁ := b5e146
               have i₂ := b5e30250
               grind)
            | exact superpose b5e30250 b5e146
            | exact resolve b5e146 b5e30250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e146 b5e30250
          have b5e30591 : x = y := by grind
          clear b5e30543
          have b5e30751 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e137
               have i₂ := b5e30591
               grind)
            | exact superpose b5e30591 b5e137
            | exact resolve b5e137 b5e30591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e137 b5e30591
          have b5e30794 : False := by grind
          exact b5e30794
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e24 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e28 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e26
        have b6e29 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e28
          | exact resolve b6e28 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e30 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e29
             grind)
          | exact superpose b6e29 b6e13
          | exact resolve b6e13 b6e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e31 : x = (k x y) := by
          first
          | (have i₁ := b6e30
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e30
          | exact resolve b6e30 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e53 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e31
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e31 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e58 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e53
             have r₂ := b6e21
             grind)
          | exact resolve b6e53 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e62 : x = (M.op x y) := by
          first
          | (have r₁ := b6e58
             have r₂ := b6e20
             grind)
          | exact resolve b6e58 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e74 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e62
             grind)
          | exact superpose b6e62 b6e23
          | exact resolve b6e23 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e75 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e62
             grind)
          | exact superpose b6e62 b6e20
          | exact resolve b6e20 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e135 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e52 X0 x
             have i₂ := b6e24 (σ X0)
             grind)
          | exact superpose b6e24 b6e52
          | (have j0 := b6e52 X0 x
             grind)
          | exact resolve b6e52 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e1230 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e24 (σ x)
             have i₂ := b6e135 x
             grind)
          | exact superpose b6e135 b6e24
          | (have j1 := b6e135 x
             grind)
          | exact resolve b6e24 b6e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e135
        have b6e1252 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by grind
        clear b6e1230
        have b6e1265 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e1252
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1252
          | exact resolve b6e1252 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1252
        have b6e1287 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have r₁ := b6e1265
             have r₂ := b6e74
             grind)
          | exact resolve b6e1265 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74 b6e1265
        have b6e1294 : (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b6e1287
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1287
          | exact resolve b6e1287 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1287
        have b6e1307 : (τ (σ y)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1294
             grind)
          | exact superpose b6e1294 b6e13
          | exact resolve b6e13 b6e1294
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1294
        have b6e1348 : y = (k x x) := by
          first
          | (have i₁ := b6e1307
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1307
          | exact resolve b6e1307 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1307
        have b6e1468 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e1348
             grind)
          | exact superpose b6e1348 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e1348
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1469 : x = (M.op x x) ∨ y = (M.op x x) := by grind
        clear b6e1468
        have b6e1532 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e15 x x
             have i₂ := b6e1469
             grind)
          | exact superpose b6e1469 b6e15
          | (have j0 := b6e15 x x
             grind)
          | (have r₁ := b6e15 x x
             have r₂ := b6e1469
             grind)
          | exact resolve b6e15 b6e1469
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1469
        have b6e1541 : x = (k x x) ∨ y = (M.op x x) := by grind
        clear b6e1532
        have b6e1543 : x = y ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e1541
             have i₂ := b6e1348
             grind)
          | exact superpose b6e1348 b6e1541
          | exact resolve b6e1541 b6e1348
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1348 b6e1541
        have b6e1547 : y = (M.op x x) := by
          first
          | (have r₁ := b6e1543
             have r₂ := b6e75
             grind)
          | exact resolve b6e1543 b6e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75 b6e1543
        have b6e1793 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x x
             have i₂ := b6e1547
             grind)
          | exact superpose b6e1547 b6e12
          | exact resolve b6e12 b6e1547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2081 : y = (M.op x y) := by
          first
          | (have i₁ := b6e1547
             have i₂ := b6e1793 x
             grind)
          | exact superpose b6e1793 b6e1547
          | exact resolve b6e1547 b6e1793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1547 b6e1793
        have b6e2089 : False := by grind
        exact b6e2089
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b7e25 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
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
          have b7e27 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) := by
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
          have b7e29 : (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e27
          have b7e30 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e29
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e29
            | exact resolve b7e29 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e31 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e30
               grind)
            | exact superpose b7e30 b7e14
            | exact resolve b7e14 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e32 : y = (k y x) := by
            first
            | (have i₁ := b7e31
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e31
            | exact resolve b7e31 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b7e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e61 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e32
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e32 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e64 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e21
               grind)
            | exact resolve b7e61 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e68 : y = (M.op y x) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e82 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e22
            | exact resolve b7e22 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e137 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e59 X0 y
               have i₂ := b7e25 (σ X0)
               grind)
            | exact superpose b7e25 b7e59
            | (have j0 := b7e59 X0 y
               grind)
            | exact resolve b7e59 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e164 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X0) (σ X1)
               have i₂ := b7e59 X0 X1
               grind)
            | exact superpose b7e59 b7e17
            | (have j0 := b7e17 (σ X0) (σ X1)
               have j1 := b7e59 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e59 X0 X1
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X0)
               have r₂ := b7e59 X0 X1
               grind)
            | exact resolve b7e17 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e172 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e164 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e164
          have b7e173 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e172 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e172
          have b7e177 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e173 X0 X1
               have j1 := b7e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b7e173 X0 X1
               have r₂ := b7e16 (σ X0) (σ X1)
               grind)
            | exact resolve b7e173 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e173
          have b7e197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e177 X0 X1
               have i₂ := b7e19 X0 X1
               grind)
            | exact superpose b7e19 b7e177
            | (have j0 := b7e177 X0 X1
               grind)
            | exact resolve b7e177 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e177
          have b7e670 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e197 (τ X0) X1
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e197
            | exact resolve b7e197 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e197
          have b7e730 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e670 X0 X1
               have i₂ := b7e33 X0 X1
               grind)
            | exact superpose b7e33 b7e670
            | (have j0 := b7e670 X0 X1
               grind)
            | exact resolve b7e670 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e670
          have b7e741 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e730 X0 X1
               have i₂ := b7e33 X0 X1
               grind)
            | exact superpose b7e33 b7e730
            | (have j0 := b7e730 X0 X1
               grind)
            | exact resolve b7e730 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e730
          have b7e1210 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e25 (σ y)
               have i₂ := b7e137 y
               grind)
            | exact superpose b7e137 b7e25
            | (have j1 := b7e137 y
               grind)
            | exact resolve b7e25 b7e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e137
          have b7e1232 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y y)) := by grind
          clear b7e1210
          have b7e1247 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e1232
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1232
            | exact resolve b7e1232 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1232
          have b7e1270 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1247
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1247
            | exact resolve b7e1247 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1247
          have b7e1286 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1270
               grind)
            | exact superpose b7e1270 b7e14
            | exact resolve b7e14 b7e1270
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1270
          have b7e1328 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1286
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1286
            | exact resolve b7e1286 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1286
          have b7e4063 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e741 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e741
            | exact resolve b7e741 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e741
          have b7e4161 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e4063 y y
               have i₂ := b7e1328
               grind)
            | exact superpose b7e1328 b7e4063
            | exact resolve b7e4063 b7e1328
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1328 b7e4063
          have b7e4248 : x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e4161
               have r₂ := b7e82
               grind)
            | exact resolve b7e4161 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e4161
          have b7e4525 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 y y
               have i₂ := b7e4248
               grind)
            | exact superpose b7e4248 b7e13
            | exact resolve b7e13 b7e4248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e5821 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e4248
               have i₂ := b7e4525 y
               grind)
            | exact superpose b7e4525 b7e4248
            | exact resolve b7e4248 b7e4525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4248 b7e4525
          have b7e5823 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
          clear b7e5821
          have b7e5825 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e5823
               have r₂ := b7e22
               grind)
            | exact resolve b7e5823 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5823
          have b7e5884 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e5825
               grind)
            | exact superpose b7e5825 b7e23
            | exact resolve b7e23 b7e5825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e5885 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e5825
               grind)
            | exact superpose b7e5825 b7e24
            | exact resolve b7e24 b7e5825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5825
          have b7e5967 : False := by grind
          exact b7e5967
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
          have b8e95 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e109 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e95
          have b8e116 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e109
               have r₂ := b8e23
               grind)
            | exact resolve b8e109 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e139 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e116
               grind)
            | exact superpose b8e116 b8e20
            | exact resolve b8e20 b8e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e191 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e139
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e139
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e139 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e192 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e191
          have b8e193 : y = (M.op x y) := by
            first
            | (have r₁ := b8e192
               have r₂ := b8e22
               grind)
            | exact resolve b8e192 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192
          have b8e194 : False := by grind
          exact b8e194

/-- `Equation327`: `x ◇ y = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then Y else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_y_y_pyx_Equation327 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law327 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law327.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e65 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e65 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e65 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e65 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e68 (σ X0) (σ X1)
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e68
          | exact resolve b1e68 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e1353 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k x X0)) ∨ (σ X0) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b1e26 (σ X0)
             have i₂ := b1e92 x X0
             grind)
          | exact superpose b1e92 b1e26
          | (have j1 := b1e92 x X0
             grind)
          | exact resolve b1e26 b1e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e92
        have b1e66055 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1353 x
             grind)
          | exact superpose b1e1353 b1e21
          | (have j1 := b1e1353 x
             grind)
          | exact resolve b1e21 b1e1353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1353
        have b1e66197 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e66055
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e66055
          | (have j1 := b1e17 x x
             grind)
          | exact resolve b1e66055 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66055
        have b1e66203 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e66197
        have b1e66209 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e66203
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e66203
          | exact resolve b1e66203 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66203
        have b1e66220 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e66209
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e66209
          | exact resolve b1e66209 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66209
        have b1e66221 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b1e66220
        have b1e66230 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e66221
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e66221
          | exact resolve b1e66221 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66221
        have b1e66237 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e66230
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e66230
          | exact resolve b1e66230 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66230
        have b1e66242 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e66237
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e66237
          | exact resolve b1e66237 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e66237
        have b1e66246 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e66242
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e66242
          | exact resolve b1e66242 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66242
        have b1e66339 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e66246
             grind)
          | exact superpose b1e66246 b1e13
          | exact resolve b1e13 b1e66246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66246
        have b1e66463 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e66339
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e66339
          | exact resolve b1e66339 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66339
        have b1e66464 : x = y := by grind
        clear b1e66463
        have b1e66585 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e66464
             grind)
          | exact superpose b1e66464 b1e21
          | exact resolve b1e21 b1e66464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66639 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e66585
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e66585
          | exact resolve b1e66585 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66585
        have b1e66640 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e66639
             have i₂ := b1e66464
             grind)
          | exact superpose b1e66464 b1e66639
          | exact resolve b1e66639 b1e66464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66464 b1e66639
        have b1e66641 : False := by grind
        exact b1e66641
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
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
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
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
        have b2e28 : y ≠ y ∨ y = (k x y) := by
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
        have b2e29 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op X1 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 X0)
             have r₂ := b2e12 X0 X0 X0
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 x
             have i₂ := b2e25 X0
             grind)
          | exact superpose b2e25 b2e15
          | (have j0 := b2e15 X0 x
             grind)
          | exact resolve b2e15 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : y = (k x y) := by grind
        clear b2e28
        have b2e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e32 X0 X1
             grind)
          | exact superpose b2e32 b2e13
          | exact resolve b2e13 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b2e49 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) ∨ (M.op (τ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X1 X0
             have i₂ := b2e17 (τ X1) X0
             grind)
          | exact superpose b2e17 b2e32
          | (have j1 := b2e17 (τ X1) X0
             grind)
          | exact resolve b2e32 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
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
        have b2e53 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e55 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 X2
             have i₂ := b2e17 X0 X2
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 (M.op X1 X2) X1
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X0 X2
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e57 X0 X1
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e57 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e33 X1 X0
             grind)
          | exact superpose b2e33 b2e13
          | exact resolve b2e13 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e59 (σ X0) (σ X1)
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e59
          | exact resolve b2e59 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e77 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e33 X0 X1
             have i₂ := b2e59 X1 (τ X0)
             grind)
          | exact superpose b2e59 b2e33
          | (have j1 := b2e59 X1 (τ X0)
             grind)
          | exact resolve b2e33 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X1 X0
             have i₂ := b2e59 (τ X1) X0
             grind)
          | exact superpose b2e59 b2e32
          | (have j1 := b2e59 (τ X1) X0
             grind)
          | exact resolve b2e32 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e83 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e106 : x ≠ y ∨ x = (k x x) := by
          first
          | (have i₁ := b2e30 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e30
          | (have j0 := b2e30 x
             grind)
          | exact resolve b2e30 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e115 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e29 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e142 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X2 X0
             have i₂ := b2e55 X1 X0 X0
             grind)
          | (have i₁ := b2e17 X0 X0
             have i₂ := b2e55 X0 X0 X2
             grind)
          | exact superpose b2e55 b2e17
          | (have j0 := b2e17 X2 X0
             have j1 := b2e55 X2 X1 X0
             grind)
          | exact resolve b2e17 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e156 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X2 X0
             have i₂ := b2e55 X0 X0 X1
             grind)
          | (have i₁ := b2e17 X0 X2
             have i₂ := b2e55 X0 X2 X2
             grind)
          | exact superpose b2e55 b2e17
          | (have j0 := b2e17 X0 X1
             have j1 := b2e55 X0 X1 X1
             grind)
          | exact resolve b2e17 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e190 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e32 X0 (M.op (τ X0) (τ X0))
             have i₂ := b2e115 (τ X0)
             grind)
          | exact superpose b2e115 b2e32
          | exact resolve b2e32 b2e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e192 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e52 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e193 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e192
             have r₂ := b2e21
             grind)
          | exact resolve b2e192 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e192
        have b2e194 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e193
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e193
          | exact resolve b2e193 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e193
        have b2e195 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e194
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e194
          | exact resolve b2e194 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e194
        have b2e207 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e37 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e37
          | exact resolve b2e37 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e277 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e72 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e115 (σ X0)
             grind)
          | exact superpose b2e115 b2e72
          | exact resolve b2e72 b2e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115
        have b2e373 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e48 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e374 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e373 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e373
        have b2e428 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X1 X2) X0) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e83 (M.op X1 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e83
          | (have j0 := b2e83 X1 X0
             grind)
          | exact resolve b2e83 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e614 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e59 (τ X1) (τ X0)
             have i₂ := b2e207 X0 X1
             grind)
          | exact superpose b2e207 b2e59
          | exact resolve b2e59 b2e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e756 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op (σ x) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e428 (σ y) (σ x) X0
             have i₂ := b2e195
             grind)
          | exact superpose b2e195 b2e428
          | (have j0 := b2e428 (σ y) (σ x) X0
             grind)
          | (have r₁ := b2e428 (σ y) (σ x) x
             have r₂ := b2e195
             grind)
          | exact resolve b2e428 b2e195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e195 b2e428
        have b2e761 : ∀ X0 : G, (σ y) = (k (M.op (σ x) X0) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e756 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e756
        have b2e873 : ∀ X0 : G, (k (τ (M.op (σ x) X0)) y) = (τ (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e37 (M.op (σ x) X0) y
             have i₂ := b2e761 X0
             grind)
          | exact superpose b2e761 b2e37
          | exact resolve b2e37 b2e761
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e761
        have b2e882 : ∀ X0 : G, y = (k (τ (M.op (σ x) X0)) y) := by
          intro X0
          first
          | (have i₁ := b2e873 X0
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e873
          | exact resolve b2e873 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e873
        have b2e900 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e374 (τ X0)
             have i₂ := b2e33 X0 (τ X0)
             grind)
          | exact superpose b2e33 b2e374
          | (have j0 := b2e374 (τ X0)
             grind)
          | exact resolve b2e374 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e904 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e900 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e900
          | (have j0 := b2e900 X0
             grind)
          | exact resolve b2e900 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e900
        have b2e908 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e904 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e904
          | (have j0 := b2e904 X0
             grind)
          | exact resolve b2e904 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e904
        have b2e944 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e908 (τ X0)
             have i₂ := b2e207 X0 X0
             grind)
          | exact superpose b2e207 b2e908
          | (have j0 := b2e908 (τ X0)
             grind)
          | exact resolve b2e908 b2e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1029 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (σ X1) (σ X0)
             have i₂ := b2e76 X0 X1
             grind)
          | exact superpose b2e76 b2e12
          | (have j1 := b2e76 X0 X1
             grind)
          | exact resolve b2e12 b2e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1128 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (k x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e77 X0 x
             have i₂ := b2e25 (τ X0)
             grind)
          | exact superpose b2e25 b2e77
          | (have j0 := b2e77 X0 x
             grind)
          | exact resolve b2e77 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e3001 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e190 x
             have i₂ := b2e49 (τ x) x
             grind)
          | exact superpose b2e49 b2e190
          | (have j1 := b2e49 (τ X0) X0
             grind)
          | exact resolve b2e190 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e3002 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (k X0 (σ (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e190 x
             have i₂ := b2e80 (τ x) x
             grind)
          | exact superpose b2e80 b2e190
          | (have j1 := b2e80 (τ X0) X0
             grind)
          | exact resolve b2e190 b2e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e80 b2e190
        have b2e3028 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have j0 := b2e3001 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3001
        have b2e3042 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e3002 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e3002
          | (have j0 := b2e3002 X0
             grind)
          | exact resolve b2e3002 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3002
        have b2e3043 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e3028 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e3028
          | (have j0 := b2e3028 X0
             grind)
          | exact resolve b2e3028 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3028
        have b2e3054 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3042 X0
             have i₂ := b2e207 X0 X0
             grind)
          | exact superpose b2e207 b2e3042
          | (have j0 := b2e3042 X0
             grind)
          | exact resolve b2e3042 b2e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3042
        have b2e8160 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e142 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e142
        have b2e8162 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e8160 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8160
        have b2e8163 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e8162 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8162
        have b2e8452 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e72 X0 (k (σ X0) (σ X0))
             have i₂ := b2e3054 (σ X0)
             grind)
          | exact superpose b2e3054 b2e72
          | (have j1 := b2e3054 (σ X0)
             grind)
          | exact resolve b2e72 b2e3054
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3054
        have b2e8462 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e8452 x
             have i₂ := b2e37 (σ x) x
             grind)
          | exact superpose b2e37 b2e8452
          | (have j0 := b2e8452 X0
             grind)
          | exact resolve b2e8452 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8452
        have b2e8478 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e8462 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e8462
          | (have j0 := b2e8462 X0
             grind)
          | exact resolve b2e8462 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8462
        have b2e8493 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k X0 (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e8478 X0
             have i₂ := b2e37 (σ X0) X0
             grind)
          | exact superpose b2e37 b2e8478
          | (have j0 := b2e8478 X0
             grind)
          | exact resolve b2e8478 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8478
        have b2e8507 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e8493 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e8493
          | (have j0 := b2e8493 X0
             grind)
          | exact resolve b2e8493 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8493
        have b2e8913 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e156 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e156
        have b2e8915 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e8913 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8913
        have b2e8916 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e8915 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8915
        have b2e9197 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e8916 (σ X0)
             grind)
          | exact superpose b2e8916 b2e18
          | (have j1 := b2e8916 (σ X0)
             grind)
          | exact resolve b2e18 b2e8916
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8916
        have b2e32668 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ x) (σ X0)) ∨ (k x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1128 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1128
          | exact resolve b2e1128 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1128
        have b2e32825 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 y)) ∨ (k x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e32668 X0
             have i₂ := b2e18 x X0
             grind)
          | exact superpose b2e18 b2e32668
          | (have j0 := b2e32668 X0
             grind)
          | exact resolve b2e32668 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32668
        have b2e34306 : ∀ X0 X1 : G, (k (τ X1) (k x X0)) = (τ (k X1 (σ (M.op X0 y)))) ∨ (k x X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e37 X1 (k x X0)
             have i₂ := b2e32825 X0
             grind)
          | exact superpose b2e32825 b2e37
          | (have j1 := b2e32825 X0
             grind)
          | exact resolve b2e37 b2e32825
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32825
        have b2e34418 : ∀ X0 X1 : G, (k (τ X1) (k x X0)) = (k (τ X1) (M.op X0 y)) ∨ (k x X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e34306 X0 X1
             have i₂ := b2e37 X1 (M.op X0 y)
             grind)
          | exact superpose b2e37 b2e34306
          | (have j0 := b2e34306 X0 X1
             grind)
          | exact resolve b2e34306 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34306
        have b2e48120 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e72 X0 (k (σ X0) (σ X0))
             have i₂ := b2e3043 (σ X0)
             grind)
          | exact superpose b2e3043 b2e72
          | (have j1 := b2e3043 (σ X0)
             grind)
          | exact resolve b2e72 b2e3043
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72 b2e3043
        have b2e48130 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e48120 x
             have i₂ := b2e37 (σ x) x
             grind)
          | exact superpose b2e37 b2e48120
          | (have j0 := b2e48120 X0
             grind)
          | exact resolve b2e48120 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e48120
        have b2e48145 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e48130 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e48130
          | (have j0 := b2e48130 X0
             grind)
          | exact resolve b2e48130 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48130
        have b2e48157 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e48145 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e48145
          | (have j0 := b2e48145 X0
             grind)
          | exact resolve b2e48145 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48145
        have b2e61100 : y = (k (τ (σ (k x x))) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e882 (σ x)
             have i₂ := b2e9197 x
             grind)
          | exact superpose b2e9197 b2e882
          | (have j1 := b2e9197 x
             grind)
          | exact resolve b2e882 b2e9197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e882
        have b2e61135 : y = (k (k x x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e61100
             have i₂ := b2e13 (k x x)
             grind)
          | exact superpose b2e13 b2e61100
          | exact resolve b2e61100 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61100
        have b2e61405 : y = (k (M.op x x) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e61135
             have i₂ := b2e8163 x x
             grind)
          | exact superpose b2e8163 b2e61135
          | (have j1 := b2e8163 (σ x) (σ x)
             grind)
          | exact resolve b2e61135 b2e8163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61135
        have b2e61419 : y = (k (M.op x x) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e61405
        have b2e61424 : y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e61419
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e61419
          | exact resolve b2e61419 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61419
        have b2e61433 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e61424
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e61424
          | exact resolve b2e61424 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61424
        have b2e61438 : x = (M.op x y) ∨ y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e61433
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e61433
          | exact resolve b2e61433 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61433
        have b2e61442 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e61438
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e61438
          | exact resolve b2e61438 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61438
        have b2e61461 : (τ (σ x)) = (k x (τ (σ x))) ∨ y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e277 x
             have i₂ := b2e61442
             grind)
          | exact superpose b2e61442 b2e277
          | exact resolve b2e277 b2e61442
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277 b2e61442
        have b2e61520 : x = (k x x) ∨ y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e61461
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e61461
          | exact resolve b2e61461 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61461
        have b2e61527 : x = (k x x) ∨ y = (k y y) := by
          first
          | (have r₁ := b2e61520
             have r₂ := b2e106
             grind)
          | exact resolve b2e61520 b2e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106 b2e61520
        have b2e61584 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e944 x
             have i₂ := b2e61527
             grind)
          | exact superpose b2e61527 b2e944
          | (have j0 := b2e944 x
             grind)
          | exact resolve b2e944 b2e61527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e944
        have b2e61602 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e8163 x x
             have i₂ := b2e61527
             grind)
          | exact superpose b2e61527 b2e8163
          | (have j0 := b2e8163 x x
             grind)
          | exact resolve b2e8163 b2e61527
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8163 b2e61527
        have b2e61603 : x = (M.op x x) ∨ y = (k y y) := by grind
        clear b2e61602
        have b2e61609 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (k y y) := by grind
        clear b2e61584
        have b2e61619 : x = (M.op x y) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e61603
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e61603
          | exact resolve b2e61603 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61603
        have b2e61642 : y = (k y y) ∨ x = y := by
          first
          | (have i₁ := b2e61619
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e61619
          | exact resolve b2e61619 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61619
        have b2e61688 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e374 y
             have i₂ := b2e61642
             grind)
          | exact superpose b2e61642 b2e374
          | (have j0 := b2e374 y
             grind)
          | exact resolve b2e374 b2e61642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61642
        have b2e61736 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
        clear b2e61688
        have b2e62304 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e61736
             grind)
          | exact superpose b2e61736 b2e22
          | exact resolve b2e22 b2e61736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61736
        have b2e62771 : (τ x) = (τ (k x x)) ∨ (τ x) = (τ (k x x)) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e614 x x
             have i₂ := b2e61609
             grind)
          | exact superpose b2e61609 b2e614
          | (have j0 := b2e614 x x
             grind)
          | exact resolve b2e614 b2e61609
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e614 b2e61609
        have b2e62813 : (τ x) = (τ (k x x)) ∨ y = (k y y) := by grind
        clear b2e62771
        have b2e62954 : ∀ X0 : G, (τ (k X0 (k x x))) = (k (τ X0) (τ x)) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e207 (k x x) X0
             have i₂ := b2e62813
             grind)
          | exact superpose b2e62813 b2e207
          | exact resolve b2e207 b2e62813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62955 : ∀ X0 : G, (k (τ x) (τ X0)) = (τ (k (k x x) X0)) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e207 X0 (k x x)
             have i₂ := b2e62813
             grind)
          | exact superpose b2e62813 b2e207
          | exact resolve b2e207 b2e62813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62813
        have b2e63021 : ∀ X0 : G, (τ (k x X0)) = (τ (k (k x x) X0)) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e62955 X0
             have i₂ := b2e207 X0 x
             grind)
          | exact superpose b2e207 b2e62955
          | exact resolve b2e62955 b2e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62955
        have b2e63022 : ∀ X0 : G, (τ (k X0 x)) = (τ (k X0 (k x x))) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e62954 X0
             have i₂ := b2e207 x X0
             grind)
          | exact superpose b2e207 b2e62954
          | exact resolve b2e62954 b2e207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e207 b2e62954
        have b2e68722 : ∀ X0 : G, (σ (τ (k x X0))) = (k (k x x) X0) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e14 (k (k x x) X0)
             have i₂ := b2e63021 X0
             grind)
          | exact superpose b2e63021 b2e14
          | exact resolve b2e14 b2e63021
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63021
        have b2e68749 : ∀ X0 : G, (k x X0) = (k (k x x) X0) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e68722 X0
             have i₂ := b2e14 (k x X0)
             grind)
          | exact superpose b2e14 b2e68722
          | exact resolve b2e68722 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68722
        have b2e69087 : ∀ X0 : G, (k X0 (k x x)) = (σ (τ (k X0 x))) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e14 (k X0 (k x x))
             have i₂ := b2e63022 X0
             grind)
          | exact superpose b2e63022 b2e14
          | exact resolve b2e14 b2e63022
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63022
        have b2e69113 : ∀ X0 : G, (k X0 x) = (k X0 (k x x)) ∨ y = (k y y) := by
          intro X0
          first
          | (have i₁ := b2e69087 X0
             have i₂ := b2e14 (k X0 x)
             grind)
          | exact superpose b2e14 b2e69087
          | exact resolve b2e69087 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69087
        have b2e69203 : (k x x) ≠ (k (k x x) x) ∨ (k x x) = (M.op (k x x) (k x x)) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e908 (k x x)
             have i₂ := b2e69113 (k x x)
             grind)
          | exact superpose b2e69113 b2e908
          | (have j0 := b2e908 (k x x)
             grind)
          | (have r₁ := b2e908 y
             have r₂ := b2e69113 x
             grind)
          | exact resolve b2e908 b2e69113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69113
        have b2e69304 : (k x x) = (M.op (k x x) (k x x)) ∨ y = (k y y) := by
          first
          | (have r₁ := b2e69203
             have r₂ := b2e68749 x
             grind)
          | exact resolve b2e69203 b2e68749
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68749 b2e69203
        have b2e72497 : (k x x) ≠ (k x x) ∨ (k x x) = (k (k x x) (k x x)) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e83 (k x x) (k x x)
             have i₂ := b2e69304
             grind)
          | exact superpose b2e69304 b2e83
          | (have j0 := b2e83 (k x x) (k x x)
             grind)
          | (have r₁ := b2e83 (k x x) (k x x)
             have r₂ := b2e69304
             grind)
          | exact resolve b2e83 b2e69304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83 b2e69304
        have b2e72509 : (k x x) = (k (k x x) (k x x)) ∨ y = (k y y) := by grind
        clear b2e72497
        have b2e91762 : ∀ X0 X1 : G, (k X0 (k x X1)) = (k X0 (M.op X1 y)) ∨ (k x X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e34418 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e34418
          | (have j0 := b2e34418 X1 X1
             grind)
          | exact resolve b2e34418 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34418
        have b2e91938 : (k x x) = (k x (M.op x y)) ∨ x = (k x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e8507 x
             have i₂ := b2e91762 x x
             grind)
          | exact superpose b2e91762 b2e8507
          | (have j0 := b2e8507 x
             have j1 := b2e91762 x x
             grind)
          | exact resolve b2e8507 b2e91762
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8507
        have b2e91942 : (k x x) = (k x (M.op x y)) ∨ x = (M.op x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e48157 x
             have i₂ := b2e91762 x x
             grind)
          | exact superpose b2e91762 b2e48157
          | (have j0 := b2e48157 x
             have j1 := b2e91762 x x
             grind)
          | exact resolve b2e48157 b2e91762
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48157 b2e91762
        have b2e92027 : (k x x) = (k x (M.op x y)) ∨ x = (k x x) := by grind
        clear b2e91938
        have b2e92043 : (k x x) = (k x (M.op x y)) ∨ x = (M.op x x) := by
          first
          | (have j1 := b2e908 x
             grind)
          | (have r₁ := b2e91942
             have r₂ := b2e908 x
             grind)
          | exact resolve b2e91942 b2e908
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e908 b2e91942
        have b2e92047 : (k x y) = (k x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b2e92027
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e92027
          | exact resolve b2e92027 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92027
        have b2e92067 : (k x y) = (k x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e92043
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e92043
          | exact resolve b2e92043 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92043
        have b2e92071 : x = (k x x) ∨ y = (k x x) := by
          first
          | (have i₁ := b2e92047
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e92047
          | exact resolve b2e92047 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92047
        have b2e92090 : y = (k x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e92067
             have i₂ := b2e31
             grind)
          | exact superpose b2e31 b2e92067
          | exact resolve b2e92067 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e92067
        have b2e92094 : x = (M.op x y) ∨ y = (k x x) := by
          first
          | (have i₁ := b2e92090
             have i₂ := b2e25 x
             grind)
          | exact superpose b2e25 b2e92090
          | exact resolve b2e92090 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e92090
        have b2e92097 : y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e92094
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e92094
          | exact resolve b2e92094 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92094
        have b2e92253 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e1029 x x x
             have i₂ := b2e92097
             grind)
          | exact superpose b2e92097 b2e1029
          | exact resolve b2e1029 b2e92097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1029
        have b2e92351 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b2e92253 X0
             grind)
          | (have r₁ := b2e92253 X0
             have r₂ := b2e62304
             grind)
          | exact resolve b2e92253 b2e62304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62304 b2e92253
        have b2e92459 : x ≠ y ∨ y = (k x x) := by grind
        clear b2e92071
        have b2e92486 : y = (k x x) := by
          first
          | (have r₁ := b2e92459
             have r₂ := b2e92097
             grind)
          | exact resolve b2e92459 b2e92097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92097 b2e92459
        have b2e92610 : y = (k y y) ∨ y = (k y y) := by
          first
          | (have i₁ := b2e72509
             have i₂ := b2e92486
             grind)
          | exact superpose b2e92486 b2e72509
          | exact resolve b2e72509 b2e92486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72509
        have b2e92775 : y = (k y y) := by grind
        clear b2e92610
        have b2e92895 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e374 y
             have i₂ := b2e92775
             grind)
          | exact superpose b2e92775 b2e374
          | (have j0 := b2e374 y
             grind)
          | exact resolve b2e374 b2e92775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e374 b2e92775
        have b2e92969 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e92895
        have b2e93565 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e92969
             grind)
          | exact superpose b2e92969 b2e22
          | exact resolve b2e22 b2e92969
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92969
        have b2e95581 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e92351 (σ x)
             have i₂ := b2e9197 x
             grind)
          | exact superpose b2e9197 b2e92351
          | (have j1 := b2e9197 x
             grind)
          | exact resolve b2e92351 b2e9197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9197 b2e92351
        have b2e95877 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e95581
             have i₂ := b2e92486
             grind)
          | exact superpose b2e92486 b2e95581
          | exact resolve b2e95581 b2e92486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95581
        have b2e95880 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have r₁ := b2e95877
             have r₂ := b2e21
             grind)
          | exact resolve b2e95877 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95877
        have b2e96063 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = y := by
          first
          | (have i₁ := b2e76 x x
             have i₂ := b2e95880
             grind)
          | exact superpose b2e95880 b2e76
          | (have j0 := b2e76 x x
             grind)
          | exact resolve b2e76 b2e95880
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76 b2e95880
        have b2e96137 : (σ x) = (σ (k x x)) ∨ x = y := by grind
        clear b2e96063
        have b2e96159 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e96137
             have i₂ := b2e92486
             grind)
          | exact superpose b2e92486 b2e96137
          | exact resolve b2e96137 b2e92486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92486 b2e96137
        have b2e96183 : x = y := by
          first
          | (have r₁ := b2e96159
             have r₂ := b2e93565
             grind)
          | exact resolve b2e96159 b2e93565
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96159
        have b2e96352 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e93565
             have i₂ := b2e96183
             grind)
          | exact superpose b2e96183 b2e93565
          | exact resolve b2e93565 b2e96183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93565 b2e96183
        have b2e96353 : False := by grind
        exact b2e96353
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e17 (σ X1) (σ X0)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X1) (σ X0)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e59 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e59 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e59 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e59 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e445 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e26 (σ X0)
             have i₂ := b3e52 x X0
             grind)
          | exact superpose b3e52 b3e26
          | (have j1 := b3e52 x X0
             grind)
          | exact resolve b3e26 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e471 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e445 X0
             have i₂ := b3e26 (σ x)
             grind)
          | exact superpose b3e26 b3e445
          | (have j0 := b3e445 X0
             grind)
          | exact resolve b3e445 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e445
        have b3e508 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e471 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e471
          | (have j0 := b3e471 X0
             grind)
          | exact resolve b3e471 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e471
        have b3e4498 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e26 (σ x)
             have i₂ := b3e508 x
             grind)
          | exact superpose b3e508 b3e26
          | (have j1 := b3e508 x
             grind)
          | exact resolve b3e26 b3e508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e508
        have b3e4583 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4498
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e4498
          | exact resolve b3e4498 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4498
        have b3e4616 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4583
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e4583
          | exact resolve b3e4583 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4583
        have b3e4617 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e4616
        have b3e4644 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e4617
             grind)
          | exact superpose b3e4617 b3e13
          | exact resolve b3e13 b3e4617
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4617
        have b3e4689 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4644
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4644
          | exact resolve b3e4644 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4644
        have b3e4907 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e61 x x
             have i₂ := b3e4689
             grind)
          | exact superpose b3e4689 b3e61
          | exact resolve b3e61 b3e4689
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e4689
        have b3e4915 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4907
             have i₂ := b3e25 x
             grind)
          | exact superpose b3e25 b3e4907
          | exact resolve b3e4907 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e4907
        have b3e4924 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b3e4915
             have r₂ := b3e20
             grind)
          | exact resolve b3e4915 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4915
        have b3e5184 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e4924
             grind)
          | exact superpose b3e4924 b3e13
          | exact resolve b3e13 b3e4924
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4924
        have b3e5228 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e5184
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e5184
          | exact resolve b3e5184 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5184
        have b3e5229 : x = y := by grind
        clear b3e5228
        have b3e5916 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e5229
             grind)
          | exact superpose b3e5229 b3e24
          | exact resolve b3e24 b3e5229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e5947 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e5916
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e5916
          | exact resolve b3e5916 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5916
        have b3e5949 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e5947
             have i₂ := b3e5229
             grind)
          | exact superpose b3e5229 b3e5947
          | exact resolve b3e5947 b3e5229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5229 b3e5947
        have b3e5950 : False := by grind
        exact b3e5950
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e16 X0 x
               have i₂ := b4e26 X0
               grind)
            | exact superpose b4e26 b4e16
            | (have j0 := b4e16 X0 x
               grind)
            | exact resolve b4e16 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b4e58 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e60 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2 X2
               have i₂ := b4e18 X0 X2
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 (M.op X1 X2) X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 X2
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e64 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e64 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e64 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e67 (σ X0) (σ X1)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e67
            | exact resolve b4e67 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X0 X1
               have i₂ := b4e67 X1 (τ X0)
               grind)
            | exact superpose b4e67 b4e36
            | (have j1 := b4e67 X1 (τ X0)
               grind)
            | exact resolve b4e36 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e67
          have b4e190 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 X2 X0
               have i₂ := b4e60 X1 X0 X0
               grind)
            | (have i₁ := b4e18 X0 X0
               have i₂ := b4e60 X0 X0 X2
               grind)
            | exact superpose b4e60 b4e18
            | (have j0 := b4e18 X2 X0
               have j1 := b4e60 X2 X1 X0
               grind)
            | exact resolve b4e18 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e449 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e56 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e450 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e449 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e449
          have b4e1385 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k x X0)) ∨ (σ X0) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b4e27 (σ X0)
               have i₂ := b4e90 x X0
               grind)
            | exact superpose b4e90 b4e27
            | (have j1 := b4e90 x X0
               grind)
            | exact resolve b4e27 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e1466 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (k x (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e91 X0 x
               have i₂ := b4e26 (τ X0)
               grind)
            | exact superpose b4e26 b4e91
            | (have j0 := b4e91 X0 x
               grind)
            | exact resolve b4e91 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e13605 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e190 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e190
          have b4e13607 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e13605 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13605
          have b4e13608 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e13607 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13607
          have b4e64299 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1385 x
               grind)
            | exact superpose b4e1385 b4e20
            | (have j1 := b4e1385 x
               grind)
            | exact resolve b4e20 b4e1385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1385
          have b4e64472 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op X0 y)) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e1466 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e1466
            | exact resolve b4e1466 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1466
          have b4e64538 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 y)) ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e64472 X0
               have i₂ := b4e19 x X0
               grind)
            | exact superpose b4e19 b4e64472
            | (have j0 := b4e64472 X0
               grind)
            | exact resolve b4e64472 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64472
          have b4e64797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e64299
               have i₂ := b4e64538 x
               grind)
            | exact superpose b4e64538 b4e64299
            | (have j1 := b4e64538 x
               grind)
            | (have r₁ := b4e64299
               have r₂ := b4e64538 x
               grind)
            | exact resolve b4e64299 b4e64538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64299 b4e64538
          have b4e64799 : (σ (M.op x y)) = (σ x) ∨ x = (k x x) := by grind
          clear b4e64797
          have b4e64897 : (M.op x y) = (τ (σ x)) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e64799
               grind)
            | exact superpose b4e64799 b4e14
            | exact resolve b4e14 b4e64799
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64799
          have b4e64999 : x = (M.op x y) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e64897
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e64897
            | exact resolve b4e64897 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64897
          have b4e65026 : x = (k x x) := by
            first
            | (have j1 := b4e33 x
               grind)
            | (have r₁ := b4e64999
               have r₂ := b4e33 x
               grind)
            | exact resolve b4e64999 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e64999
          have b4e65378 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e450 x
               have i₂ := b4e65026
               grind)
            | exact superpose b4e65026 b4e450
            | (have j0 := b4e450 x
               grind)
            | exact resolve b4e450 b4e65026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e450
          have b4e65405 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e13608 x x
               have i₂ := b4e65026
               grind)
            | exact superpose b4e65026 b4e13608
            | (have j0 := b4e13608 x x
               grind)
            | exact resolve b4e13608 b4e65026
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13608 b4e65026
          have b4e65406 : x = (M.op x x) := by grind
          clear b4e65405
          have b4e65427 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e65378
          have b4e65448 : x = (M.op x y) := by
            first
            | (have i₁ := b4e65406
               have i₂ := b4e26 x
               grind)
            | exact superpose b4e26 b4e65406
            | exact resolve b4e65406 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e65406
          have b4e65458 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e65427
               have i₂ := b4e27 (σ x)
               grind)
            | exact superpose b4e27 b4e65427
            | exact resolve b4e65427 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e65427
          have b4e66249 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e65458
               grind)
            | exact superpose b4e65458 b4e20
            | exact resolve b4e20 b4e65458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65458
          have b4e66366 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e66249
               have i₂ := b4e65448
               grind)
            | exact superpose b4e65448 b4e66249
            | exact resolve b4e66249 b4e65448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65448 b4e66249
          have b4e66367 : False := by grind
          exact b4e66367
        · have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : x ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b5e16 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y y
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e14
            | exact resolve b5e14 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b5e51 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e56 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e56 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e56 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e56 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
            intro X0
            grind
          have b5e82 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e84 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e77 X0
               have j1 := b5e82 (M.op X0 X0) X0
               grind)
            | (have r₁ := b5e77 x
               have r₂ := b5e82 (M.op x x) x
               grind)
            | exact resolve b5e77 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e82
          have b5e85 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e84 X0
               have j1 := b5e16 (M.op X0 X0) X0
               grind)
            | (have r₁ := b5e84 x
               have r₂ := b5e16 (M.op x x) x
               grind)
            | exact resolve b5e84 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e212 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b5e37 (M.op (σ X0) (σ X0)) X0
               have i₂ := b5e85 (σ X0)
               grind)
            | exact superpose b5e85 b5e37
            | exact resolve b5e37 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e85
          have b5e220 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e212 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e212
            | exact resolve b5e212 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e212
          have b5e336 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e48 y y
               grind)
            | exact superpose b5e48 b5e24
            | (have j1 := b5e48 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e48 y x
               grind)
            | exact resolve b5e24 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e384 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e48 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e385 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e384 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e384
          have b5e394 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e336
          have b5e992 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e394
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e394
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e394 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e394
          have b5e993 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e992
          have b5e994 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e993
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e993
            | exact resolve b5e993 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e993
          have b5e995 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e994
          have b5e1002 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e995
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e995
            | exact resolve b5e995 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e995
          have b5e1063 : y = (k (τ (σ y)) y) ∨ x = y := by
            first
            | (have i₁ := b5e220 y
               have i₂ := b5e1002
               grind)
            | exact superpose b5e1002 b5e220
            | exact resolve b5e220 b5e1002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220 b5e1002
          have b5e1088 : y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e1063
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e1063
            | exact resolve b5e1063 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1063
          have b5e1090 : y = (k y y) := by
            first
            | (have r₁ := b5e1088
               have r₂ := b5e28
               grind)
            | exact resolve b5e1088 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e1088
          have b5e1102 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e385 y
               have i₂ := b5e1090
               grind)
            | exact superpose b5e1090 b5e385
            | (have j0 := b5e385 y
               grind)
            | exact resolve b5e385 b5e1090
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e385
          have b5e1105 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e1090
               grind)
            | exact superpose b5e1090 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e1090
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1090
          have b5e1106 : y = (M.op y y) := by grind
          clear b5e1105
          have b5e1109 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e1102
          have b5e1177 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e1106
               grind)
            | exact superpose b5e1106 b5e22
            | exact resolve b5e22 b5e1106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1106
          have b5e1250 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1177
               grind)
            | exact superpose b5e1177 b5e23
            | exact resolve b5e23 b5e1177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1177
          have b5e1265 : False := by grind
          exact b5e1265
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
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
        have b6e25 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
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
        have b6e41 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
        have b6e44 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have j1 := b6e15 (M.op (σ x) (σ y)) (σ x)
             grind)
          | (have r₁ := b6e41
             have r₂ := b6e15 (M.op (σ x) (σ y)) (σ x)
             grind)
          | exact resolve b6e41 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e45 : (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e44
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e44
          | exact resolve b6e44 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e46 : (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e45
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e45
          | exact resolve b6e45 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b6e53 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
        have b6e55 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e60 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e60 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e60 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e60 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e65 : y = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e53
             have r₂ := b6e21
             grind)
          | exact resolve b6e53 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e71 : y = (M.op y x) := by
          first
          | (have r₁ := b6e65
             have r₂ := b6e20
             grind)
          | exact resolve b6e65 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e80 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e46
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e46
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e46 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e87 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e80
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e80
          | exact resolve b6e80 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80
        have b6e424 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e25 (σ X0)
             have i₂ := b6e52 x X0
             grind)
          | exact superpose b6e52 b6e25
          | (have j1 := b6e52 x X0
             grind)
          | exact resolve b6e25 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e450 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e424 X0
             have i₂ := b6e25 (σ x)
             grind)
          | exact superpose b6e25 b6e424
          | (have j0 := b6e424 X0
             grind)
          | exact resolve b6e424 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e424
        have b6e492 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e450 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e450
          | (have j0 := b6e450 X0
             grind)
          | exact resolve b6e450 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e450
        have b6e2607 : (σ x) ≠ (σ y) ∨ x = y ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e24
          | exact resolve b6e24 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e3144 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e25 (σ x)
             have i₂ := b6e492 x
             grind)
          | exact superpose b6e492 b6e25
          | (have j1 := b6e492 x
             grind)
          | exact resolve b6e25 b6e492
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25 b6e492
        have b6e3225 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3144
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3144
          | exact resolve b6e3144 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3144
        have b6e3259 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3225
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3225
          | exact resolve b6e3225 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3225
        have b6e3260 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3259
        have b6e3290 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3260
             grind)
          | exact superpose b6e3260 b6e13
          | exact resolve b6e13 b6e3260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3260
        have b6e3325 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3290
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3290
          | exact resolve b6e3290 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3290
        have b6e3492 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e63 x x
             have i₂ := b6e3325
             grind)
          | exact superpose b6e3325 b6e63
          | exact resolve b6e63 b6e3325
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e3325
        have b6e3497 : y = (M.op x x) ∨ x = y := by
          first
          | (have r₁ := b6e3492
             have r₂ := b6e2607
             grind)
          | exact resolve b6e3492 b6e2607
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2607 b6e3492
        have b6e3717 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x x
             have i₂ := b6e3497
             grind)
          | exact superpose b6e3497 b6e12
          | exact resolve b6e12 b6e3497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4516 : y = (M.op x y) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b6e3497
             have i₂ := b6e3717 x
             grind)
          | exact superpose b6e3717 b6e3497
          | exact resolve b6e3497 b6e3717
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3497 b6e3717
        have b6e4565 : y = (M.op x y) ∨ x = y := by grind
        clear b6e4516
        have b6e4570 : x = y := by
          first
          | (have r₁ := b6e4565
             have r₂ := b6e20
             grind)
          | exact resolve b6e4565 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4565
        have b6e4991 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e4570
             grind)
          | exact superpose b6e4570 b6e24
          | exact resolve b6e24 b6e4570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e4997 : y = (M.op y y) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e4570
             grind)
          | exact superpose b6e4570 b6e71
          | exact resolve b6e71 b6e4570
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71 b6e4570
        have b6e5010 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b6e4991
             have i₂ := b6e4997
             grind)
          | exact superpose b6e4997 b6e4991
          | exact resolve b6e4991 b6e4997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4991 b6e4997
        have b6e5011 : False := by grind
        exact b6e5011
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e35 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b7e40 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b7e16 (σ x) (σ y)
               grind)
            | (have r₁ := b7e35
               have r₂ := b7e16 (σ x) (σ y)
               grind)
            | exact resolve b7e35 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e41 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e40
            | exact resolve b7e40 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e44 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e41
               grind)
            | exact superpose b7e41 b7e14
            | exact resolve b7e14 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : y = (k x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e44
            | exact resolve b7e44 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e18 (σ X1) (σ X0)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X1) (σ X0)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e55 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e61 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e61 X0 X1
               have j1 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e61 X0 X1
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e61 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e70 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e71 : y = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e22
               grind)
            | exact resolve b7e70 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : y = (M.op y x) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e21
               grind)
            | exact resolve b7e71 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e405 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e53 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e53
            | exact resolve b7e53 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e479 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e405
          have b7e762 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e479
               grind)
            | exact superpose b7e479 b7e14
            | exact resolve b7e14 b7e479
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e479
          have b7e784 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e762
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e762
            | exact resolve b7e762 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e762
          have b7e824 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e64 y y
               have i₂ := b7e784
               grind)
            | exact superpose b7e784 b7e64
            | exact resolve b7e64 b7e784
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e784
          have b7e829 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e824
               have r₂ := b7e22
               grind)
            | exact resolve b7e824 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e824
          have b7e906 : x = (τ (σ y)) ∨ x = y := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e829
               grind)
            | exact superpose b7e829 b7e14
            | exact resolve b7e14 b7e829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e829
          have b7e930 : x = y ∨ x = y := by
            first
            | (have i₁ := b7e906
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e906
            | exact resolve b7e906 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e906
          have b7e931 : x = y := by grind
          clear b7e930
          have b7e1010 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e931
               grind)
            | exact superpose b7e931 b7e21
            | exact resolve b7e21 b7e931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1017 : y = (M.op y y) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e931
               grind)
            | exact superpose b7e931 b7e73
            | exact resolve b7e73 b7e931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e931
          have b7e1025 : False := by grind
          exact b7e1025
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e27 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X0 (M.op X1 X2)
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e16
            | (have j0 := b8e16 X0 (M.op X1 X2)
               grind)
            | (have r₁ := b8e16 X0 (M.op X0 X0)
               have r₂ := b8e13 X0 X0 X0
               grind)
            | exact resolve b8e16 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b8e29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e28 X0 X1
               grind)
            | exact superpose b8e28 b8e14
            | exact resolve b8e14 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e50 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b8e52 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e54 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 X2
               have i₂ := b8e18 X0 X2
               grind)
            | (have i₁ := b8e13 X0 X1 X2
               have i₂ := b8e18 (M.op X1 X2) X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X2
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e55 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X0 ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X1 X2) X1 X2
               have i₂ := b8e18 X0 (M.op X1 X2)
               grind)
            | (have i₁ := b8e13 X0 X1 X2
               have i₂ := b8e18 (M.op X0 (M.op X1 X2)) X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 (M.op X1 X2)
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e56 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
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
          have b8e57 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e58 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e55 X0 X1 X2
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e55
            | (have j0 := b8e55 X0 X1 X2
               grind)
            | exact resolve b8e55 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e57 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e57 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e57 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e33 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e33
            | exact resolve b8e33 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e59 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e59
            | exact resolve b8e59 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e28 X1 X0
               have i₂ := b8e59 (τ X1) X0
               grind)
            | exact superpose b8e59 b8e28
            | (have j1 := b8e59 (τ X1) X0
               grind)
            | exact resolve b8e28 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e78 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e115 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b8e27 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e145 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e18 X2 X0
               have i₂ := b8e54 X1 X0 X0
               grind)
            | (have i₁ := b8e18 X0 X0
               have i₂ := b8e54 X0 X0 X2
               grind)
            | exact superpose b8e54 b8e18
            | (have j0 := b8e18 X2 X0
               have j1 := b8e54 X2 X1 X0
               grind)
            | exact resolve b8e18 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e203 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e56 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e204 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e203
               have r₂ := b8e23
               grind)
            | exact resolve b8e203 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e203
          have b8e205 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e204
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e204
            | exact resolve b8e204 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204
          have b8e320 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e50 X0 X0
               have i₂ := b8e50 X0 X1
               grind)
            | exact superpose b8e50 b8e50
            | (have j0 := b8e50 X1 X0
               have j1 := b8e50 X1 X0
               grind)
            | exact resolve b8e50 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e375 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X2)) = X1 ∨ (σ X0) = (M.op X1 (σ X2)) ∨ (σ (k X2 X0)) = (M.op (σ X0) (σ X2)) ∨ (σ X2) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e58 X0 (σ X1) (σ X0)
               have i₂ := b8e50 X0 X1
               grind)
            | exact superpose b8e50 b8e58
            | (have j1 := b8e50 X0 X2
               grind)
            | exact resolve b8e58 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50 b8e58
          have b8e391 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b8e320 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e320
          have b8e962 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e77
            | exact resolve b8e77 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e1003 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e962 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e962
            | (have j0 := b8e962 X0 X1
               grind)
            | exact resolve b8e962 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e962
          have b8e1083 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e72 y x
               grind)
            | exact superpose b8e72 b8e20
            | (have j1 := b8e72 y x
               grind)
            | exact resolve b8e20 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1092 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 (σ X1) (σ X0)
               have i₂ := b8e72 X0 X1
               grind)
            | exact superpose b8e72 b8e13
            | (have j1 := b8e72 X0 X1
               grind)
            | exact resolve b8e13 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e4984 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e1083
               have i₂ := b8e1003 y x
               grind)
            | exact superpose b8e1003 b8e1083
            | (have j1 := b8e1003 y x
               grind)
            | (have r₁ := b8e1083
               have r₂ := b8e1003 y x
               grind)
            | exact resolve b8e1083 b8e1003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1003
          have b8e4985 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
          clear b8e4984
          have b8e5199 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e4985
               grind)
            | exact superpose b8e4985 b8e14
            | exact resolve b8e14 b8e4985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4985
          have b8e5252 : x = (M.op x y) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e5199
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e5199
            | exact resolve b8e5199 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5199
          have b8e5254 : x = (k y x) := by
            first
            | (have j1 := b8e78 y x
               grind)
            | (have r₁ := b8e5252
               have r₂ := b8e78 y x
               grind)
            | exact resolve b8e5252 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5252
          have b8e7588 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e145 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145
          have b8e7590 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e7588 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7588
          have b8e7591 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e7590 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7590
          have b8e11007 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e391 y x
               grind)
            | exact superpose b8e391 b8e20
            | (have j1 := b8e391 y x
               grind)
            | exact resolve b8e20 b8e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e391
          have b8e11371 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e11007
               have i₂ := b8e5254
               grind)
            | exact superpose b8e5254 b8e11007
            | exact resolve b8e11007 b8e5254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11007
          have b8e11420 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e11371
               have i₂ := b8e205
               grind)
            | exact superpose b8e205 b8e11371
            | exact resolve b8e11371 b8e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e205 b8e11371
          have b8e27831 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e1083
               have i₂ := b8e7591 y x
               grind)
            | exact superpose b8e7591 b8e1083
            | (have j1 := b8e7591 y x
               grind)
            | exact resolve b8e1083 b8e7591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1083
          have b8e27833 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b8e27831
          have b8e27877 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b8e27833
               have r₂ := b8e21
               grind)
            | exact resolve b8e27833 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27833
          have b8e49920 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            grind
          clear b8e375
          have b8e50476 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e49920 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49920
          have b8e50501 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e50476 X0 X1
               have j1 := b8e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b8e50476 X0 X1
               have r₂ := b8e16 (σ X0) (σ X1)
               grind)
            | (have r₁ := b8e50476 X1 X1
               have r₂ := b8e16 (σ X1) (σ X1)
               grind)
            | exact resolve b8e50476 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50476
          have b8e50517 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e50501 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e50501
            | (have j0 := b8e50501 X0 X1
               grind)
            | exact resolve b8e50501 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50501
          have b8e50520 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e50517 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e50517
            | (have j0 := b8e50517 X0 X1
               grind)
            | exact resolve b8e50517 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50517
          have b8e50521 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b8e50520 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50520
          have b8e55093 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1092 (τ X1) (τ X0) X2
               have i₂ := b8e61 X0 X1
               grind)
            | exact superpose b8e61 b8e1092
            | exact resolve b8e1092 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e1092
          have b8e55151 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e55093 X0 X1 X2
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e55093
            | (have j0 := b8e55093 X0 X1 X2
               grind)
            | exact resolve b8e55093 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55093
          have b8e55155 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e55151 X0 X1 X2
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e55151
            | (have j0 := b8e55151 X0 X1 X2
               grind)
            | exact resolve b8e55151 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55151
          have b8e55157 : ∀ X0 X1 X2 : G, (k X0 X1) = (σ (τ X1)) ∨ (M.op X2 X1) = (M.op X2 (k X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e55155 X0 X1 X2
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e55155
            | (have j0 := b8e55155 X0 X1 X2
               grind)
            | exact resolve b8e55155 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55155
          have b8e55159 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e55157 X0 X1 X2
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e55157
            | (have j0 := b8e55157 X0 X1 X2
               grind)
            | exact resolve b8e55157 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55157
          have b8e68866 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e115 (σ X0)
               have i₂ := b8e50521 X0 X1
               grind)
            | exact superpose b8e50521 b8e115
            | (have j1 := b8e50521 X1 X0
               grind)
            | exact resolve b8e115 b8e50521
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115 b8e50521
          have b8e68872 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e68866 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e68866
            | (have j0 := b8e68866 X0 X1
               grind)
            | exact resolve b8e68866 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68866
          have b8e68873 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e68872 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68872
          have b8e68912 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e68873 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e68873
            | exact resolve b8e68873 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68944 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e68873 y x
               grind)
            | exact superpose b8e68873 b8e20
            | (have j1 := b8e68873 y x
               grind)
            | exact resolve b8e20 b8e68873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68873
          have b8e68996 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b8e68944
               have i₂ := b8e5254
               grind)
            | exact superpose b8e5254 b8e68944
            | exact resolve b8e68944 b8e5254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5254 b8e68944
          have b8e69010 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 (τ X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e68912 X0 X1
               have i₂ := b8e28 X0 X1
               grind)
            | exact superpose b8e28 b8e68912
            | (have j0 := b8e68912 X0 X1
               grind)
            | exact resolve b8e68912 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28 b8e68912
          have b8e69015 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e69010 X0 X1
               have i₂ := b8e29 X0 X1
               grind)
            | exact superpose b8e29 b8e69010
            | (have j0 := b8e69010 X0 X1
               grind)
            | exact resolve b8e69010 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29 b8e69010
          have b8e69519 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e68996
               have i₂ := b8e27877
               grind)
            | exact superpose b8e27877 b8e68996
            | (have r₁ := b8e68996
               have r₂ := b8e27877
               grind)
            | exact resolve b8e68996 b8e27877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68996
          have b8e69522 : (σ y) = (σ (k x y)) ∨ x = (M.op y x) := by grind
          clear b8e69519
          have b8e69570 : (k x y) = (τ (σ y)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e14 (k x y)
               have i₂ := b8e69522
               grind)
            | exact superpose b8e69522 b8e14
            | exact resolve b8e14 b8e69522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69522
          have b8e69652 : y = (k x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e69570
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e69570
            | exact resolve b8e69570 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69570
          have b8e69705 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e7591 x y
               have i₂ := b8e69652
               grind)
            | exact superpose b8e69652 b8e7591
            | (have j0 := b8e7591 x y
               grind)
            | exact resolve b8e7591 b8e69652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7591 b8e69652
          have b8e69710 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e69705
          have b8e69714 : x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e69710
               have r₂ := b8e21
               grind)
            | exact resolve b8e69710 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69710
          have b8e69742 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 y x
               have i₂ := b8e69714
               grind)
            | exact superpose b8e69714 b8e13
            | exact resolve b8e13 b8e69714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70018 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e69714
               have i₂ := b8e69742 y
               grind)
            | exact superpose b8e69742 b8e69714
            | exact resolve b8e69714 b8e69742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69714
          have b8e70168 : y ≠ (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e69742
          have b8e70185 : x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e70018
               have r₂ := b8e70168
               grind)
            | exact resolve b8e70018 b8e70168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70018 b8e70168
          have b8e70190 : y = (M.op y x) := by
            first
            | (have r₁ := b8e70185
               have r₂ := b8e22
               grind)
            | exact resolve b8e70185 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70185
          have b8e70213 : y ≠ y ∨ y = (k x y) := by
            first
            | (have i₁ := b8e78 x y
               have i₂ := b8e70190
               grind)
            | exact superpose b8e70190 b8e78
            | (have j0 := b8e78 x y
               grind)
            | (have r₁ := b8e78 x y
               have r₂ := b8e70190
               grind)
            | exact resolve b8e78 b8e70190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e70267 : y = (k x y) := by grind
          clear b8e70213
          have b8e71495 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e11420
               have i₂ := b8e27877
               grind)
            | exact superpose b8e27877 b8e11420
            | (have r₁ := b8e11420
               have r₂ := b8e27877
               grind)
            | exact resolve b8e11420 b8e27877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11420 b8e27877
          have b8e71498 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
          clear b8e71495
          have b8e71500 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e71498
               have i₂ := b8e70267
               grind)
            | exact superpose b8e70267 b8e71498
            | exact resolve b8e71498 b8e70267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70267 b8e71498
          have b8e71501 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ x = (M.op y x) := by grind
          clear b8e71500
          have b8e71504 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b8e71501
               have i₂ := b8e70190
               grind)
            | exact superpose b8e70190 b8e71501
            | exact resolve b8e71501 b8e70190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71501
          have b8e73300 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e69015 X0 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e69015
            | exact resolve b8e69015 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69015
          have b8e74374 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b8e14 (k x x)
               have i₂ := b8e71504
               grind)
            | exact superpose b8e71504 b8e14
            | exact resolve b8e14 b8e71504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71504
          have b8e74442 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b8e74374
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e74374
            | exact resolve b8e74374 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74374
          have b8e74554 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e55159 x x x
               have i₂ := b8e74442
               grind)
            | exact superpose b8e74442 b8e55159
            | exact resolve b8e55159 b8e74442
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55159
          have b8e74566 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b8e73300 x x
               have i₂ := b8e74442
               grind)
            | exact superpose b8e74442 b8e73300
            | exact resolve b8e73300 b8e74442
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73300 b8e74442
          have b8e74567 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b8e74566
          have b8e74577 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b8e74554 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74554
          have b8e77111 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e74567
               have i₂ := b8e74577 x
               grind)
            | exact superpose b8e74577 b8e74567
            | exact resolve b8e74567 b8e74577
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74567 b8e74577
          have b8e77195 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b8e77111
          have b8e77201 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b8e77195
               have r₂ := b8e21
               grind)
            | exact resolve b8e77195 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77195
          have b8e77235 : x = (τ (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e14 x
               have i₂ := b8e77201
               grind)
            | exact superpose b8e77201 b8e14
            | exact resolve b8e14 b8e77201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77201
          have b8e77365 : x = y ∨ x = y := by
            first
            | (have i₁ := b8e77235
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e77235
            | exact resolve b8e77235 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77235
          have b8e77366 : x = y := by grind
          clear b8e77365
          have b8e77375 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e77366
               grind)
            | exact superpose b8e77366 b8e21
            | exact resolve b8e21 b8e77366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77465 : y = (M.op y y) := by
            first
            | (have i₁ := b8e70190
               have i₂ := b8e77366
               grind)
            | exact superpose b8e77366 b8e70190
            | exact resolve b8e70190 b8e77366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70190 b8e77366
          have b8e77509 : False := by grind
          exact b8e77509

/-- `Equation3272`: `x ◇ x = y ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3272 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3272 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3272.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e61 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e64 : False := by grind
      exact b0e64
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
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b5e55 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e57 : x = y ∨ x = (k x y) := by grind
          clear b5e55
          have b5e58 : x = (k x y) := by
            first
            | (have r₁ := b5e57
               have r₂ := b5e21
               grind)
            | exact resolve b5e57 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e266 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e4074 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e266 x y
               have i₂ := b5e58
               grind)
            | exact superpose b5e58 b5e266
            | (have j0 := b5e266 x y
               grind)
            | exact resolve b5e266 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e266
          have b5e4077 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e4074
          have b5e4080 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e4077
               have r₂ := b5e24
               grind)
            | exact resolve b5e4077 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4077
          have b5e4084 : False := by grind
          exact b5e4084
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
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b7e58 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e48
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e48 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e26
               grind)
            | exact resolve b7e58 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e58
          have b7e60 : x = y := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e22
               grind)
            | exact resolve b7e59 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e61 : False := by grind
          exact b7e61
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
          have b8e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e256 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e262 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e256
               have r₂ := b8e24
               grind)
            | exact resolve b8e256 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256
          have b8e268 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e262
               have r₂ := b8e23
               grind)
            | exact resolve b8e262 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e262
          have b8e271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e268
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e268
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e268
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e268
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e268 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e268
          have b8e272 : x = (M.op x y) ∨ x = y := by grind
          clear b8e271
          have b8e273 : x = y := by
            first
            | (have r₁ := b8e272
               have r₂ := b8e22
               grind)
            | exact resolve b8e272 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e274 : False := by grind
          exact b8e274

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3273 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e33 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op X1 x)
           have i₂ := b0e11 X0 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 x X0
           have i₂ := b0e33 x X1
           grind)
        | exact superpose b0e33 b0e33
        | exact resolve b0e33 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (M.op X0 X0)) := by
        intro X0
        grind
      have b0e44 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X1 X1
           have i₂ := b0e33 X1 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e49 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e40 X0
           have i₂ := b0e44 X0 X0
           grind)
        | exact superpose b0e44 b0e40
        | exact resolve b0e40 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e44
      have b0e83 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e49 X1
           have i₂ := b0e39 y X0
           grind)
        | (have i₁ := b0e49 X1
           have i₂ := b0e39 X0 y
           grind)
        | exact superpose b0e39 b0e49
        | exact resolve b0e49 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e49
      have b0e86 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        grind
      clear b0e24
      have b0e91 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e86 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e86
        | exact resolve b0e86 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86
      have b0e92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        grind
      clear b0e91
      have b0e93 : False := by grind
      exact b0e93
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
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b5e52 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e55 : x = y ∨ x = (k x y) := by grind
          clear b5e52
          have b5e56 : x = (k x y) := by
            first
            | (have r₁ := b5e55
               have r₂ := b5e21
               grind)
            | exact resolve b5e55 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e1327 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e13514 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1327 x y
               have i₂ := b5e56
               grind)
            | exact superpose b5e56 b5e1327
            | (have j0 := b5e1327 x y
               grind)
            | exact resolve b5e1327 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56 b5e1327
          have b5e13517 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e13514
          have b5e13520 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e13517
               have r₂ := b5e24
               grind)
            | exact resolve b5e13517 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13517
          have b5e13524 : False := by grind
          exact b5e13524
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
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b7e56 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e59 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e56
          have b7e60 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e23
               grind)
            | exact resolve b7e59 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e61 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e60
            | exact resolve b7e60 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e70 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e61
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e61
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e61 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e71 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e26
               grind)
            | exact resolve b7e70 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e70
          have b7e72 : x = y := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e22
               grind)
            | exact resolve b7e71 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e73 : False := by grind
          exact b7e73
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
          have b8e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e977 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e75 x y
               grind)
            | exact superpose b8e75 b8e20
            | (have j1 := b8e75 x y
               grind)
            | exact resolve b8e20 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e990 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e977
               have r₂ := b8e24
               grind)
            | exact resolve b8e977 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e977
          have b8e996 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e990
               have r₂ := b8e23
               grind)
            | exact resolve b8e990 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e990
          have b8e1001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e996
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e996
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e996
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e996
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e996 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e996
          have b8e1002 : x = (M.op x y) ∨ x = y := by grind
          clear b8e1001
          have b8e1003 : x = y := by
            first
            | (have r₁ := b8e1002
               have r₂ := b8e22
               grind)
            | exact resolve b8e1002 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1002
          have b8e1004 : False := by grind
          exact b8e1004

/-- `Equation3274`: `x ◇ x = y ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxx_x_pxy_Equation3274 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3274 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3274.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e47 (σ X0)
           grind)
        | exact superpose b0e47 b0e17
        | exact resolve b0e17 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e55 X0
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e55
        | exact resolve b0e55 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e55
      have b0e421 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e23
           have i₂ := b0e60 y
           grind)
        | exact superpose b0e60 b0e23
        | (have r₁ := b0e23
           have r₂ := b0e60 y
           grind)
        | exact resolve b0e23 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e60
      have b0e437 : False := by grind
      exact b0e437
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
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
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
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
        have b2e32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X0 (M.op X1 X0)) X2 x
             have i₂ := b2e12 X0 x X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X1 X0) X2 X0
             have i₂ := b2e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e32 X0 X1 X2
             have i₂ := b2e12 X0 (M.op X0 (M.op X1 X0)) X1
             grind)
          | (have i₁ := b2e32 X0 X1 X2
             have i₂ := b2e12 (M.op X0 (M.op X1 X0)) X1 X2
             grind)
          | exact superpose b2e12 b2e32
          | exact resolve b2e32 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e51 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : (M.op x x) = (k x y) := by grind
        clear b2e51
        have b2e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e54 (σ X0)
             grind)
          | exact superpose b2e54 b2e18
          | exact resolve b2e18 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e59 X0
             have i₂ := b2e54 X0
             grind)
          | exact superpose b2e54 b2e59
          | exact resolve b2e59 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e59
        have b2e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e76 X0 X1
             have i₂ := b2e66 X1
             grind)
          | exact superpose b2e66 b2e76
          | (have j0 := b2e76 X0 X1
             grind)
          | exact resolve b2e76 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e145 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e33 X1 x X3
             have i₂ := b2e33 X1 x X0
             grind)
          | (have i₁ := b2e33 X0 X0 x
             have i₂ := b2e33 X0 X1 (M.op X0 X0)
             grind)
          | exact superpose b2e33 b2e33
          | exact resolve b2e33 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e467 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e92 x y
             grind)
          | exact superpose b2e92 b2e21
          | (have j1 := b2e92 x y
             grind)
          | exact resolve b2e21 b2e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e469 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (M.op (σ X1) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X1) X2 (σ X0)
             have i₂ := b2e92 X0 X1
             grind)
          | exact superpose b2e92 b2e12
          | (have j1 := b2e92 X0 X1
             grind)
          | exact resolve b2e12 b2e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92
        have b2e510 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op X2 (M.op (σ X1) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e469 X0 X1 X2
             have i₂ := b2e66 X1
             grind)
          | exact superpose b2e66 b2e469
          | (have j0 := b2e469 X0 X1 X2
             grind)
          | exact resolve b2e469 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e469
        have b2e511 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e467
             have r₂ := b2e24
             grind)
          | exact resolve b2e467 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467
        have b2e533 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e511
             have r₂ := b2e22
             grind)
          | exact resolve b2e511 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e511
        have b2e546 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e533
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e533
          | exact resolve b2e533 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e533
        have b2e551 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e546
             have i₂ := b2e66 y
             grind)
          | exact superpose b2e66 b2e546
          | exact resolve b2e546 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e546
        have b2e997 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e34 X1 x X2
             have i₂ := b2e145 (M.op X1 (M.op x X1)) X1 X0
             grind)
          | (have i₁ := b2e34 X1 x X2
             have i₂ := b2e145 X0 X1 (M.op X1 (M.op x X1))
             grind)
          | exact superpose b2e145 b2e34
          | exact resolve b2e34 b2e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e145
        have b2e2457 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e997 X0 (σ X0) X2
             have i₂ := b2e66 X0
             grind)
          | exact superpose b2e66 b2e997
          | exact resolve b2e997 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66 b2e997
        have b2e51577 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (σ y) (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e510 x y X0
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e510
          | (have j0 := b2e510 x y x
             grind)
          | exact resolve b2e510 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e510
        have b2e52013 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (σ y) (σ (M.op x x)))) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have j0 := b2e51577 X0
             grind)
          | (have r₁ := b2e51577 X0
             have r₂ := b2e24
             grind)
          | exact resolve b2e51577 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e51577
        have b2e52135 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (σ y) (σ (M.op x x)))) := by
          intro X0
          first
          | (have j0 := b2e52013 X0
             grind)
          | (have r₁ := b2e52013 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e52013 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52013
        have b2e52226 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e52135 x
             have i₂ := b2e2457 x x (σ y)
             grind)
          | exact superpose b2e2457 b2e52135
          | exact resolve b2e52135 b2e2457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2457 b2e52135
        have b2e52293 : False := by grind
        exact b2e52293
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e31 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X0 (M.op X1 X0)) X2 x
             have i₂ := b6e12 X0 x X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X1 X0) X2 X0
             have i₂ := b6e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e31 X0 X1 X2
             have i₂ := b6e12 X0 (M.op X0 (M.op X1 X0)) X1
             grind)
          | (have i₁ := b6e31 X0 X1 X2
             have i₂ := b6e12 (M.op X0 (M.op X1 X0)) X1 X2
             grind)
          | exact superpose b6e12 b6e31
          | exact resolve b6e31 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e52 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e55 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e52
        have b6e57 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e55
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e55
          | exact resolve b6e55 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e97 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e57
             grind)
          | exact superpose b6e57 b6e15
          | exact resolve b6e15 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e101 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e97
        have b6e102 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e101
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e101
          | exact resolve b6e101 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101
        have b6e103 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e102
             have i₂ := b6e54 x
             grind)
          | exact superpose b6e54 b6e102
          | exact resolve b6e102 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e102
        have b6e132 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e103
             grind)
          | exact superpose b6e103 b6e13
          | exact resolve b6e13 b6e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e103
        have b6e133 : (k x y) = (M.op x x) := by
          first
          | (have i₁ := b6e132
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e132
          | exact resolve b6e132 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e132
        have b6e171 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 X1
             have i₂ := b6e32 X1 X0 X1
             grind)
          | exact superpose b6e32 b6e12
          | exact resolve b6e12 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e190 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e133
             grind)
          | exact superpose b6e133 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e133
        have b6e191 : (M.op x y) = (M.op x x) ∨ x = y := by
          first
          | (have r₁ := b6e190
             have r₂ := b6e20
             grind)
          | exact resolve b6e190 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e190
        have b6e193 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e191
             have r₂ := b6e21
             grind)
          | exact resolve b6e191 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e191
        have b6e248 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x (M.op x y)) (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b6e33 x x x
             have i₂ := b6e193
             grind)
          | exact superpose b6e193 b6e33
          | exact resolve b6e33 b6e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e249 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b6e32 x x x
             have i₂ := b6e193
             grind)
          | exact superpose b6e193 b6e32
          | exact resolve b6e32 b6e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e193
        have b6e258 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b6e248 X0
             have i₂ := b6e249 (M.op x (M.op x y))
             grind)
          | exact superpose b6e249 b6e248
          | exact resolve b6e248 b6e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e248 b6e249
        have b6e259 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e258 x
             have i₂ := b6e171 x y x
             grind)
          | exact superpose b6e171 b6e258
          | exact resolve b6e258 b6e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e171 b6e258
        have b6e260 : False := by grind
        exact b6e260
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e45 (σ X0)
               grind)
            | exact superpose b8e45 b8e19
            | exact resolve b8e19 b8e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e49 X0
               have i₂ := b8e45 X0
               grind)
            | exact superpose b8e45 b8e49
            | exact resolve b8e49 b8e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45 b8e49
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e62 X0 X1
               have i₂ := b8e54 X1
               grind)
            | exact superpose b8e54 b8e62
            | (have j0 := b8e62 X0 X1
               grind)
            | exact resolve b8e62 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e459 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e76 x y
               grind)
            | exact superpose b8e76 b8e20
            | (have j1 := b8e76 x y
               grind)
            | exact resolve b8e20 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e502 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e459
               have r₂ := b8e24
               grind)
            | exact resolve b8e459 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e459
          have b8e11904 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e502
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e502
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e502
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e502
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e502 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e502
          have b8e11905 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b8e11904
          have b8e11908 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have r₁ := b8e11905
               have r₂ := b8e21
               grind)
            | exact resolve b8e11905 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11905
          have b8e11912 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e11908
               have r₂ := b8e22
               grind)
            | exact resolve b8e11908 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11908
          have b8e11916 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e11912
               grind)
            | exact superpose b8e11912 b8e23
            | exact resolve b8e23 b8e11912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11912
          have b8e11969 : False := by grind
          exact b8e11969

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pxy_Equation3284 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3284 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e26 X0 X1
           grind)
        | exact superpose b0e26 b0e12
        | exact resolve b0e12 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
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
      have b0e36 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) := by
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
      have b0e41 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X2)))) = X2 := by
        intro X0 X1 X2
        grind
      have b0e43 : ∀ X0 : G, (M.op X0 y) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 X0
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        grind
      have b0e50 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e43 X0
           have i₂ := b0e43 X1
           grind)
        | (have i₁ := b0e43 X0
           have i₂ := b0e43 y
           grind)
        | exact superpose b0e43 b0e43
        | exact resolve b0e43 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e35 X0
           have i₂ := b0e43 X0
           grind)
        | (have i₁ := b0e35 y
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e35
        | exact resolve b0e35 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e35 y
           have i₂ := b0e43 X0
           grind)
        | (have i₁ := b0e35 X0
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e35
        | exact resolve b0e35 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e90 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) X0 X0
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e11
        | exact resolve b0e11 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e123 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X1 X0 (M.op X0 (σ y))
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e41
        | exact resolve b0e41 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e131 : ∀ X0 X1 : G, (M.op X0 y) = (k (M.op X0 y) (M.op X1 (M.op X1 y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X1 y (M.op X0 y)
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e41
        | exact resolve b0e41 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e53
      have b0e145 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) := by
        intro X0
        first
        | (have i₁ := b0e131 X0 x
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e131
        | exact resolve b0e131 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e131
      have b0e149 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e123 X0 x
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e123
        | exact resolve b0e123 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e123
      have b0e713 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e90 X0
           have i₂ := b0e90 X1
           grind)
        | (have i₁ := b0e90 X0
           have i₂ := b0e90 (σ y)
           grind)
        | exact superpose b0e90 b0e90
        | exact resolve b0e90 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90
      have b0e805 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e713 (σ x) X0
           grind)
        | (have i₁ := b0e18
           have i₂ := b0e713 X0 (σ x)
           grind)
        | exact superpose b0e713 b0e18
        | exact resolve b0e18 b0e713
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e713
      have b0e826 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op X1 (M.op X1 (M.op X2 (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (σ X0) X1 X2
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e11
        | (have j1 := b0e47 X0
           grind)
        | exact resolve b0e11 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e836 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e47 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1003 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e805 X1
           have i₂ := b0e50 x X0
           grind)
        | (have i₁ := b0e805 X1
           have i₂ := b0e50 X0 x
           grind)
        | exact superpose b0e50 b0e805
        | exact resolve b0e805 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e805
      have b0e2278 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (k (τ (M.op X0 (σ y))) y) := by
        intro X0
        first
        | (have i₁ := b0e32 (M.op X0 (σ y)) y
           have i₂ := b0e149 X0
           grind)
        | exact superpose b0e149 b0e32
        | exact resolve b0e32 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e149
      have b0e35212 : ∀ X0 X1 X2 : G, (k X2 (σ (τ X2))) = (M.op X0 (M.op X0 (M.op X1 (σ (τ X2))))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e26 X2 (τ X2)
           have i₂ := b0e826 (τ X2) X0 X1
           grind)
        | exact superpose b0e826 b0e26
        | (have j1 := b0e826 (τ X2) X1 X2
           grind)
        | exact resolve b0e26 b0e826
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e826
      have b0e35587 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35212 X0 X1 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e35212
        | (have j0 := b0e35212 X0 X1 X2
           grind)
        | exact resolve b0e35212 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35212
      have b0e35652 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = (k X2 X2) ∨ (M.op X2 X2) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35587 X0 X1 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e35587
        | (have j0 := b0e35587 X0 X1 X2
           grind)
        | exact resolve b0e35587 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35587
      have b0e48707 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (k y y) ∨ y = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e35652 X0 X0 y
           have i₂ := b0e43 X0
           grind)
        | (have i₁ := b0e35652 X0 y y
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e35652
        | (have j0 := b0e35652 X1 X0 y
           grind)
        | exact resolve b0e35652 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e48768 : ∀ X0 : G, (M.op X0 y) = (k y y) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e35652 X0 y y
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e35652
        | (have j0 := b0e35652 X0 x y
           grind)
        | exact resolve b0e35652 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e35652
      have b0e49378 : ∀ X0 : G, (M.op y y) = (k y y) ∨ y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e48707 X0 x
           have i₂ := b0e11 y x X0
           grind)
        | exact superpose b0e11 b0e48707
        | (have j0 := b0e48707 X0 x
           grind)
        | exact resolve b0e48707 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48707
      have b0e51697 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (k y y)) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e1003 x X0
           have i₂ := b0e48768 x
           grind)
        | exact superpose b0e48768 b0e1003
        | exact resolve b0e1003 b0e48768
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48768
      have b0e54298 : (M.op y y) = (k y y) ∨ y = (k y y) := by
        first
        | (have i₁ := b0e145 x
           have i₂ := b0e49378 x
           grind)
        | exact superpose b0e49378 b0e145
        | exact resolve b0e145 b0e49378
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145 b0e49378
      have b0e58002 : y ≠ (M.op y y) ∨ y = (k y y) := by grind
      clear b0e54298
      have b0e72109 : (σ (k y y)) ≠ (σ (k y y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e51697 (σ y)
           have i₂ := b0e47 y
           grind)
        | exact superpose b0e47 b0e51697
        | (have j1 := b0e47 y
           grind)
        | (have r₁ := b0e51697 (σ y)
           have r₂ := b0e47 y
           grind)
        | exact resolve b0e51697 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e72126 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
      clear b0e72109
      have b0e73062 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e2278 (σ y)
           have i₂ := b0e72126
           grind)
        | exact superpose b0e72126 b0e2278
        | exact resolve b0e2278 b0e72126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2278
      have b0e73064 : (σ y) ≠ (σ (k y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e51697 (σ y)
           have i₂ := b0e72126
           grind)
        | exact superpose b0e72126 b0e51697
        | exact resolve b0e51697 b0e72126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51697
      have b0e73069 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
      clear b0e72126
      have b0e73190 : (σ y) ≠ (σ (k y y)) ∨ y = (M.op y y) := by grind
      clear b0e73064
      have b0e73266 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e73069
           have i₂ := b0e17 y y
           grind)
        | exact superpose b0e17 b0e73069
        | exact resolve b0e73069 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73069
      have b0e73268 : y = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e73062
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e73062
        | exact resolve b0e73062 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73062
      have b0e73317 : y = (M.op y y) := by
        first
        | (have r₁ := b0e73266
           have r₂ := b0e73190
           grind)
        | exact resolve b0e73266 b0e73190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73190 b0e73266
      have b0e73319 : y = (k y y) := by
        first
        | (have r₁ := b0e73268
           have r₂ := b0e58002
           grind)
        | exact resolve b0e73268 b0e58002
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58002 b0e73268
      have b0e73783 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e1003 y X0
           have i₂ := b0e73317
           grind)
        | exact superpose b0e73317 b0e1003
        | exact resolve b0e1003 b0e73317
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1003 b0e73317
      have b0e74504 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e836 y
           have i₂ := b0e73319
           grind)
        | exact superpose b0e73319 b0e836
        | (have j0 := b0e836 y
           grind)
        | exact resolve b0e836 b0e73319
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e836 b0e73319
      have b0e74523 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e74504
      have b0e74534 : False := by grind
      exact b0e74534
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
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
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e27
          | exact resolve b1e27 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e29 : x = (k x y) := by grind
        have b1e30 : x = (k x x) := by
          first
          | (have i₁ := b1e29
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e29
          | exact resolve b1e29 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e903 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e61 y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e61
          | (have j0 := b1e61 x
             grind)
          | exact resolve b1e61 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e933 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have r₁ := b1e903
             have r₂ := b1e25
             grind)
          | exact resolve b1e903 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e903
        have b1e936 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e933
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e933
          | exact resolve b1e933 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e933
        have b1e939 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e936
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e936
          | exact resolve b1e936 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e936
        have b1e941 : False := by grind
        exact b1e941
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b2e103 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e27 X1 X0
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e683 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e103
        have b2e697 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e683 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e683
          | exact resolve b2e683 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e683
        have b2e724 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e40 x
             grind)
          | exact superpose b2e40 b2e21
          | (have j1 := b2e40 x
             grind)
          | exact resolve b2e21 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e5133 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e724
        have b2e5134 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e5133
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5133
          | exact resolve b2e5133 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5133
        have b2e5135 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e5134
        have b2e5136 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e5135
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5135
          | exact resolve b2e5135 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5135
        have b2e5143 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e697 x
             have i₂ := b2e5136
             grind)
          | exact superpose b2e5136 b2e697
          | exact resolve b2e697 b2e5136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e697 b2e5136
        have b2e5204 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e5143
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e5143
          | exact resolve b2e5143 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5143
        have b2e5224 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by grind
        clear b2e5204
        have b2e5225 : x = (M.op x x) ∨ x = y := by grind
        clear b2e5224
        have b2e5228 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e5225
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5225
          | exact resolve b2e5225 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5225
        have b2e5229 : x = y := by grind
        clear b2e5228
        have b2e5333 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e5229
             grind)
          | exact superpose b2e5229 b2e22
          | exact resolve b2e22 b2e5229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5229
        have b2e5363 : False := by grind
        exact b2e5363
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e29 : (σ y) = (k (σ y) (σ y)) := by grind
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
        have b3e54 : y = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b3e32
        have b3e57 : y = (M.op y y) := by grind
        clear b3e54
        have b3e60 : False := by grind
        exact b3e60
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e761 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e47
          have b4e787 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e761
          have b4e790 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e787
          have b4e791 : y = (M.op y y) := by grind
          clear b4e790
          have b4e792 : False := by grind
          exact b4e792
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : False := by grind
          exact b5e31
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b6e709 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e53 x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e53
          | exact resolve b6e53 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e2013 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e709
             grind)
          | exact superpose b6e709 b6e13
          | exact resolve b6e13 b6e709
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2027 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2013
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2013
          | exact resolve b6e2013 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2013
        have b6e2029 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2027
        have b6e2030 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2029
             have r₂ := b6e20
             grind)
          | exact resolve b6e2029 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2029
        have b6e2168 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2030
        have b6e2282 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e709
             have i₂ := b6e2168
             grind)
          | exact superpose b6e2168 b6e709
          | exact resolve b6e709 b6e2168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e709 b6e2168
        have b6e2285 : (σ x) = (σ y) := by grind
        clear b6e2282
        have b6e2438 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e2285
             grind)
          | exact superpose b6e2285 b6e13
          | exact resolve b6e13 b6e2285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2285
        have b6e2456 : x = y := by
          first
          | (have i₁ := b6e2438
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e2438
          | exact resolve b6e2438 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2438
        have b6e2464 : False := by grind
        exact b6e2464
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
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
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e29
            | exact resolve b7e29 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e31 : False := by grind
          exact b7e31
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
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
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (M.op (σ x) (σ x))
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (M.op (σ x) (σ x)) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e751 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e752 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e751
               have r₂ := b8e24
               grind)
            | exact resolve b8e751 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e751
          have b8e753 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e752
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e752
            | exact resolve b8e752 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e752
          have b8e754 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e753
               grind)
            | exact superpose b8e753 b8e20
            | exact resolve b8e20 b8e753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e753
          have b8e800 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e754
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e754
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e754
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e754
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e754 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e754
          have b8e801 : y = (M.op x x) ∨ x = y := by grind
          clear b8e800
          have b8e803 : x = y := by
            first
            | (have r₁ := b8e801
               have r₂ := b8e21
               grind)
            | exact resolve b8e801 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e801
          have b8e805 : False := by grind
          exact b8e805
