import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_x_x_pyx_Equation1043 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1043 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ x) ≠ (σ x) := by
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
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
             have i₂ := b1e12 X0 X2 X3
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e173 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
             have i₂ := b1e37 X0 X1 X2 X3
             grind)
          | exact superpose b1e37 b1e12
          | exact resolve b1e12 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e179 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e173 X0 X1 x x
             have i₂ := b1e12 X0 x x
             grind)
          | exact superpose b1e12 b1e173
          | exact resolve b1e173 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e173
        have b1e189 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e179 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e179
          | exact resolve b1e179 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e179
        have b1e209 : False := by grind
        exact b1e209
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x ≠ x ∨ x = (k x y) := by
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
        have b2e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e27 X0 X1
             grind)
          | exact superpose b2e27 b2e13
          | exact resolve b2e13 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e33 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) y)) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 (M.op (M.op X1 (M.op X0 X2)) X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X0 (M.op (M.op X1 (M.op X0 X2)) X2)
             grind)
          | (have r₁ := b2e15 X0 (M.op (M.op X1 (M.op X0 X2)) X2)
             have r₂ := b2e12 X0 X1 X2
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e36 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e38 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e12 (M.op X0 x) x y
             have i₂ := b2e33 X0
             grind)
          | exact superpose b2e33 b2e12
          | exact resolve b2e12 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e42 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b2e38 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e38
          | exact resolve b2e38 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e46 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e139 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e34 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
             have i₂ := b2e34 X0 X1 X3 X4
             grind)
          | exact superpose b2e34 b2e34
          | exact resolve b2e34 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e142 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e37 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
             have i₂ := b2e34 X0 X1 X2 X3
             grind)
          | exact superpose b2e34 b2e37
          | exact resolve b2e37 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e143 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
             have i₂ := b2e34 X0 X1 X2 X3
             grind)
          | exact superpose b2e34 b2e12
          | exact resolve b2e12 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e148 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e143 X0 X1 x x
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e143
          | exact resolve b2e143 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e143
        have b2e149 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e142 X0 X1 x x
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e142
          | exact resolve b2e142 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e142
        have b2e150 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e139 X0 X1 X2 x x
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e139
          | exact resolve b2e139 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139
        have b2e156 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e148 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e148 X0 X1
             have i₂ := b2e17 (M.op X1 X0) X1
             grind)
          | exact superpose b2e17 b2e148
          | (have j1 := b2e17 X0 X1
             grind)
          | exact resolve b2e148 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e156 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e156
        have b2e209 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 (M.op X0 (σ X1)) X1
             have i₂ := b2e149 (σ X1) X0
             grind)
          | exact superpose b2e149 b2e32
          | exact resolve b2e32 b2e149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e149
        have b2e348 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (M.op X2 (σ (k X0 X1))) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (σ X1) X2 (σ X0)
             have i₂ := b2e46 X1 X0
             grind)
          | exact superpose b2e46 b2e12
          | (have j1 := b2e46 X1 X0
             grind)
          | exact resolve b2e12 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e350 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op (M.op X2 (M.op (σ X0) X3)) X3))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e34 (σ X0) (σ X1) X2 X3
             have i₂ := b2e46 X1 X0
             grind)
          | exact superpose b2e46 b2e34
          | (have j1 := b2e46 X1 X0
             grind)
          | exact resolve b2e34 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e46
        have b2e4217 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ x)) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e348 x y X0
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e348
          | (have j0 := b2e348 x y x
             grind)
          | exact resolve b2e348 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e348
        have b2e4312 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ x)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e4217 X0
             grind)
          | (have r₁ := b2e4217 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e4217 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4217
        have b2e4334 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ x)) (σ x))) := by
          intro X0
          first
          | (have j0 := b2e4312 X0
             grind)
          | (have r₁ := b2e4312 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e4312 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4312
        have b2e4343 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b2e4334 X0
             have i₂ := b2e148 (σ x) X0
             grind)
          | exact superpose b2e148 b2e4334
          | exact resolve b2e4334 b2e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e148 b2e4334
        have b2e5327 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (M.op X0 (M.op (σ x) X1)) X1))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e350 x y X0 X1
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e350
          | (have j0 := b2e350 x y x x
             grind)
          | exact resolve b2e350 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e350
        have b2e5642 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (M.op X0 (M.op (σ x) X1)) X1))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          intro X0 X1
          first
          | (have j0 := b2e5327 X0 X1
             grind)
          | (have r₁ := b2e5327 X0 X1
             have r₂ := b2e22
             grind)
          | exact resolve b2e5327 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5327
        have b2e5673 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (σ x) (M.op (M.op X0 (M.op (σ x) X1)) X1))) := by
          intro X0 X1
          first
          | (have j0 := b2e5642 X0 X1
             grind)
          | (have r₁ := b2e5642 X0 X1
             have r₂ := b2e21
             grind)
          | exact resolve b2e5642 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5642
        have b2e5684 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e5673 x x
             have i₂ := b2e12 (σ x) x x
             grind)
          | exact superpose b2e12 b2e5673
          | exact resolve b2e5673 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5673
        have b2e6190 : (τ (σ x)) = (k (τ (σ x)) x) := by
          first
          | (have i₁ := b2e209 (σ x) x
             have i₂ := b2e5684
             grind)
          | exact superpose b2e5684 b2e209
          | exact resolve b2e209 b2e5684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e209
        have b2e6272 : x = (k x x) := by
          first
          | (have i₁ := b2e6190
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e6190
          | exact resolve b2e6190 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6190
        have b2e6625 : x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e172 x x
             have i₂ := b2e6272
             grind)
          | exact superpose b2e6272 b2e172
          | (have j0 := b2e172 x x
             grind)
          | exact resolve b2e172 b2e6272
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e172 b2e6272
        have b2e6634 : x = (M.op x x) := by grind
        clear b2e6625
        have b2e7107 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b2e150 x x x
             have i₂ := b2e6634
             grind)
          | exact superpose b2e6634 b2e150
          | exact resolve b2e150 b2e6634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e7115 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e7107 X0
             have i₂ := b2e42 X0
             grind)
          | exact superpose b2e42 b2e7107
          | exact resolve b2e7107 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e7107
        have b2e8103 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e7115 X0
             grind)
          | exact superpose b2e7115 b2e12
          | exact resolve b2e12 b2e7115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7115
        have b2e8180 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e8103 X0
             have i₂ := b2e6634
             grind)
          | exact superpose b2e6634 b2e8103
          | exact resolve b2e8103 b2e6634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6634 b2e8103
        have b2e9428 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 x) (M.op X0 (M.op X1 x))) := by
          intro X0 X1
          first
          | (have i₁ := b2e150 x X1 X0
             have i₂ := b2e8180 (M.op X0 (M.op X1 x))
             grind)
          | exact superpose b2e8180 b2e150
          | exact resolve b2e150 b2e8180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150
        have b2e9464 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e9428 X0 X0
             have i₂ := b2e8180 X0
             grind)
          | exact superpose b2e8180 b2e9428
          | exact resolve b2e9428 b2e8180
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8180 b2e9428
        have b2e10858 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 X0
             have i₂ := b2e9464 X1 X0
             grind)
          | exact superpose b2e9464 b2e12
          | exact resolve b2e12 b2e9464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e12677 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e10858 (σ x) X0
             have i₂ := b2e5684
             grind)
          | exact superpose b2e5684 b2e10858
          | exact resolve b2e10858 b2e5684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5684 b2e10858
        have b2e12977 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e4343 X0
             have i₂ := b2e12677 X0
             grind)
          | exact superpose b2e12677 b2e4343
          | exact resolve b2e4343 b2e12677
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4343 b2e12677
        have b2e13530 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e9464 (σ y) X0
             have i₂ := b2e12977 X0
             grind)
          | exact superpose b2e12977 b2e9464
          | exact resolve b2e9464 b2e12977
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9464 b2e12977
        have b2e15674 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e13530 (σ x)
             grind)
          | exact superpose b2e13530 b2e21
          | (have r₁ := b2e21
             have r₂ := b2e13530 (σ x)
             grind)
          | exact resolve b2e21 b2e13530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e13530
        have b2e15697 : False := by grind
        exact b2e15697
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
             have i₂ := b3e12 X0 X2 X3
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e173 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
             have i₂ := b3e39 X0 X1 X2 X3
             grind)
          | exact superpose b3e39 b3e12
          | exact resolve b3e12 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e178 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e173 X0 X1 x x
             have i₂ := b3e12 X0 x x
             grind)
          | exact superpose b3e12 b3e173
          | exact resolve b3e173 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e173
        have b3e190 : x = (M.op x y) := by
          first
          | (have i₁ := b3e178 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e178
          | exact resolve b3e178 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e178
        have b3e207 : False := by grind
        exact b3e207
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ (M.op x y) := by grind
          have b4e22 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e175 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b4e37 X0 X1 X2 X3
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e181 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e175 X0 X1 x x
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e175
            | exact resolve b4e175 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175
          have b4e193 : x = (M.op x y) := by
            first
            | (have i₁ := b4e181 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e181
            | exact resolve b4e181 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e181
          have b4e211 : False := by grind
          exact b4e211
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e129 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b5e34 X0 X1 X2 X3
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e134 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e129 X0 X1 x x
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e129
            | exact resolve b5e129 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129
          have b5e138 : x = (M.op x y) := by
            first
            | (have i₁ := b5e134 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e134
            | exact resolve b5e134 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e134
          have b5e159 : False := by grind
          exact b5e159
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e25 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e45 : x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
        have b6e51 : x = (M.op y x) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e45
             have r₂ := b6e21
             grind)
          | exact resolve b6e45 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e54 : x = (M.op y x) := by
          first
          | (have r₁ := b6e51
             have r₂ := b6e20
             grind)
          | exact resolve b6e51 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e56 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b6e12 y X0 x
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e12
          | exact resolve b6e12 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e82 : y = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b6e56 y
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e56
          | exact resolve b6e56 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e101 : x = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b6e12 x y x
             have i₂ := b6e82
             grind)
          | exact superpose b6e82 b6e12
          | exact resolve b6e12 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e106 : x = (M.op x x) := by
          first
          | (have i₁ := b6e101
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e101
          | exact resolve b6e101 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e101
        have b6e119 : y = (M.op y x) := by
          first
          | (have i₁ := b6e82
             have i₂ := b6e106
             grind)
          | exact superpose b6e106 b6e82
          | exact resolve b6e82 b6e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e128 : x = y := by
          first
          | (have i₁ := b6e119
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e119
          | exact resolve b6e119 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e119
        have b6e144 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e128
             grind)
          | exact superpose b6e128 b6e24
          | exact resolve b6e24 b6e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e128
        have b6e155 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e144
             have i₂ := b6e106
             grind)
          | exact superpose b6e106 b6e144
          | exact resolve b6e144 b6e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e106 b6e144
        have b6e156 : False := by grind
        exact b6e156
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e57 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          have b7e62 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b7e16 (σ x) (σ y)
               grind)
            | (have r₁ := b7e57
               have r₂ := b7e16 (σ x) (σ y)
               grind)
            | exact resolve b7e57 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e63 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e62
            | exact resolve b7e62 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e67 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e14
            | exact resolve b7e14 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e68 : x = (k x y) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e67
            | exact resolve b7e67 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e81 : x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e82 : x = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e22
               grind)
            | exact resolve b7e81 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e84 : x = (M.op y x) := by
            first
            | (have r₁ := b7e82
               have r₂ := b7e21
               grind)
            | exact resolve b7e82 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e120 : ∀ X0 X1 : G, x = (M.op x (M.op x (M.op (M.op X0 (M.op x X1)) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 x y X0 X1
               have i₂ := b7e84
               grind)
            | exact superpose b7e84 b7e31
            | exact resolve b7e31 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e133 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b7e31 X0 X1 X2 X3
               grind)
            | exact superpose b7e31 b7e13
            | exact resolve b7e13 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e138 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e133 X0 X1 x x
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e133
            | exact resolve b7e133 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e142 : x = (M.op x x) := by
            first
            | (have i₁ := b7e120 x x
               have i₂ := b7e13 x x x
               grind)
            | exact superpose b7e13 b7e120
            | exact resolve b7e120 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120
          have b7e147 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 x
               have i₂ := b7e142
               grind)
            | exact superpose b7e142 b7e13
            | exact resolve b7e13 b7e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e150 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b7e147 X0
               have i₂ := b7e138 x X0
               grind)
            | exact superpose b7e138 b7e147
            | exact resolve b7e147 b7e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138 b7e147
          have b7e194 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x x
               have i₂ := b7e150 X0
               grind)
            | exact superpose b7e150 b7e13
            | exact resolve b7e13 b7e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e202 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b7e194 X0
               have i₂ := b7e142
               grind)
            | exact superpose b7e142 b7e194
            | exact resolve b7e194 b7e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142 b7e194
          have b7e210 : x = y := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e202 y
               grind)
            | exact superpose b7e202 b7e84
            | exact resolve b7e84 b7e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84 b7e202
          have b7e261 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e210
               grind)
            | exact superpose b7e210 b7e23
            | exact resolve b7e23 b7e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e262 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e210
               grind)
            | exact superpose b7e210 b7e24
            | exact resolve b7e24 b7e210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e210
          have b7e273 : False := by grind
          exact b7e273
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
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
          have b8e28 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X1 (M.op X0 X2)) X0 X2
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e55 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e55 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e55 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e56 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e56
            | exact resolve b8e56 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e56 X1 (τ X0)
               grind)
            | exact superpose b8e56 b8e27
            | (have j1 := b8e56 X1 (τ X0)
               grind)
            | exact resolve b8e27 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e96 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e108 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e28 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
               have i₂ := b8e28 X0 X1 X3 X4
               grind)
            | exact superpose b8e28 b8e28
            | exact resolve b8e28 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e112 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
               have i₂ := b8e28 X0 X1 X2 X3
               grind)
            | exact superpose b8e28 b8e13
            | exact resolve b8e13 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e115 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op (M.op X3 (M.op X0 X4)) X4)))) = X0 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X0 X1 (M.op (M.op X2 X0) (M.op (M.op X3 (M.op X0 X4)) X4))
               have i₂ := b8e28 X0 X2 X3 X4
               grind)
            | exact superpose b8e28 b8e13
            | exact resolve b8e13 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e118 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e112 X0 X1 x x
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e112
            | exact resolve b8e112 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e120 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e108 X0 X1 X2 x x
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e108
            | exact resolve b8e108 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108
          have b8e123 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e118 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e118 X0 X1
               have i₂ := b8e18 (M.op X1 X0) X1
               grind)
            | exact superpose b8e18 b8e118
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e118 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e135 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e123 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e835 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e28 X0 X0 x X0
               have i₂ := b8e120 X0 X0 x
               grind)
            | exact superpose b8e120 b8e28
            | exact resolve b8e28 b8e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28
          have b8e925 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e120 X0 X0 X0
               have i₂ := b8e835 X0
               grind)
            | exact superpose b8e835 b8e120
            | exact resolve b8e120 b8e835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e835
          have b8e949 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
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
          have b8e990 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e949 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e949
            | (have j0 := b8e949 X0 X1
               grind)
            | exact resolve b8e949 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e949
          have b8e1018 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e88 y x
               grind)
            | exact superpose b8e88 b8e20
            | (have j1 := b8e88 y x
               grind)
            | exact resolve b8e20 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e1301 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e120 (M.op X0 X0) (M.op X0 X0) x
               have i₂ := b8e925 X0
               grind)
            | exact superpose b8e925 b8e120
            | exact resolve b8e120 b8e925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e120
          have b8e1308 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1301 X0 X1
               have i₂ := b8e29 X0 X1 X0
               grind)
            | exact superpose b8e29 b8e1301
            | exact resolve b8e1301 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29 b8e1301
          have b8e2260 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b8e1308 X0 X1
               grind)
            | exact superpose b8e1308 b8e13
            | exact resolve b8e13 b8e1308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1308
          have b8e2316 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e2260 X0 X1
               have i₂ := b8e925 X0
               grind)
            | exact superpose b8e925 b8e2260
            | exact resolve b8e2260 b8e925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e925 b8e2260
          have b8e2590 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e115 X1 X0 (M.op x (M.op X1 X1)) x X1
               have i₂ := b8e2316 (M.op (M.op x (M.op X1 X1)) X1) (M.op X0 X1)
               grind)
            | exact superpose b8e2316 b8e115
            | exact resolve b8e115 b8e2316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e14146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e1018
               have i₂ := b8e990 x y
               grind)
            | exact superpose b8e990 b8e1018
            | (have j1 := b8e990 x y
               grind)
            | (have r₁ := b8e1018
               have r₂ := b8e990 x y
               grind)
            | exact resolve b8e1018 b8e990
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e990 b8e1018
          have b8e14147 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
          clear b8e14146
          have b8e14153 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e14147
               grind)
            | exact superpose b8e14147 b8e14
            | exact resolve b8e14 b8e14147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14147
          have b8e14224 : y = (M.op x y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e14153
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e14153
            | exact resolve b8e14153 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14153
          have b8e14225 : y = (k y x) := by
            first
            | (have j1 := b8e96 y x
               grind)
            | (have r₁ := b8e14224
               have r₂ := b8e96 y x
               grind)
            | exact resolve b8e14224 b8e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e96 b8e14224
          have b8e14363 : y = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e135 y x
               have i₂ := b8e14225
               grind)
            | exact superpose b8e14225 b8e135
            | (have j0 := b8e135 y x
               grind)
            | exact resolve b8e135 b8e14225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135 b8e14225
          have b8e14572 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e2590 y x
               have i₂ := b8e14363
               grind)
            | exact superpose b8e14363 b8e2590
            | exact resolve b8e2590 b8e14363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14363
          have b8e14575 : y = (M.op x y) := by
            first
            | (have r₁ := b8e14572
               have r₂ := b8e21
               grind)
            | exact resolve b8e14572 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14572
          have b8e14806 : y = (M.op y y) := by
            first
            | (have i₁ := b8e2590 x y
               have i₂ := b8e14575
               grind)
            | exact superpose b8e14575 b8e2590
            | exact resolve b8e2590 b8e14575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2590 b8e14575
          have b8e15263 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e2316 y X0
               have i₂ := b8e14806
               grind)
            | exact superpose b8e14806 b8e2316
            | exact resolve b8e2316 b8e14806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2316 b8e14806
          have b8e16559 : x ≠ x := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e15263 x
               grind)
            | exact superpose b8e15263 b8e21
            | (have r₁ := b8e21
               have r₂ := b8e15263 x
               grind)
            | exact resolve b8e21 b8e15263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15263
          have b8e16682 : False := by grind
          exact b8e16682
