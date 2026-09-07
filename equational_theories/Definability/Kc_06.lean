import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4437`: `x ◇ (y ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pyx_pxy_Equation4437 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
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
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b0e15 X0 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have j0 := b0e15 X0 x
             grind)
          | (have r₁ := b0e15 X0 x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e27 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b0e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24
        have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X0 X1 X3
             have i₂ := b0e12 X0 X1 X2
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e43 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e12 x x x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e43 X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e43
          | exact resolve b0e43 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43
        have b0e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 X0 X1
             have i₂ := b0e17 (σ X0) (σ X1)
             grind)
          | exact superpose b0e17 b0e18
          | (have j1 := b0e17 (σ X1) (σ X1)
             grind)
          | exact resolve b0e18 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e1275 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e80 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e80
        have b0e1277 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e1275 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1275
        have b0e8765 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e1277 x
             have i₂ := b0e27 x
             grind)
          | exact superpose b0e27 b0e1277
          | (have j0 := b0e1277 x
             grind)
          | exact resolve b0e1277 b0e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e27 b0e1277
        have b0e8775 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e8765
        have b0e8847 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e38 (σ x) (σ x) x x
             have i₂ := b0e8775
             grind)
          | exact superpose b0e8775 b0e38
          | exact resolve b0e38 b0e8775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e13348 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e8775
             have i₂ := b0e8847 X0 (σ x)
             grind)
          | (have i₁ := b0e8775
             have i₂ := b0e8847 (σ x) X0
             grind)
          | exact superpose b0e8847 b0e8775
          | exact resolve b0e8775 b0e8847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8775
        have b0e13349 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e19
             have i₂ := b0e8847 X0 (σ y)
             grind)
          | (have i₁ := b0e19
             have i₂ := b0e8847 (σ y) X0
             grind)
          | exact superpose b0e8847 b0e19
          | exact resolve b0e19 b0e8847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e8847
        have b0e13475 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e13349 X0
             have i₂ := b0e48 y
             grind)
          | exact superpose b0e48 b0e13349
          | exact resolve b0e13349 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48 b0e13349
        have b0e13508 : False := by grind
        exact b0e13508
      · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
        · have b1e23 : x ≠ (M.op x x) := by grind
          have b1e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : False := by grind
          exact b1e25
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op y y) := by grind
          have b2e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b2e24 : x ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X0 X1 X3
               have i₂ := b2e13 X0 X1 X2
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e49 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e13 (σ y) (σ y) x
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e50 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e13 y y x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e51 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X0 X1 (M.op X2 (M.op X0 X1))
               have i₂ := b2e13 (M.op X0 X1) X2 X3
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e53 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e50 X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e50
            | exact resolve b2e50 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e50
          have b2e54 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e49 X0
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e49
            | exact resolve b2e49 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e49
          have b2e61 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X0 y X1
               have i₂ := b2e53 X0
               grind)
            | exact superpose b2e53 b2e13
            | exact resolve b2e13 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e66 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b2e17 y X0
               have i₂ := b2e53 X0
               grind)
            | exact superpose b2e53 b2e17
            | (have j0 := b2e17 y X0
               grind)
            | (have r₁ := b2e17 y X0
               have r₂ := b2e53 X0
               grind)
            | exact resolve b2e17 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e53
          have b2e67 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b2e66 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e66
          have b2e71 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e17 (σ y) X0
               have i₂ := b2e54 X0
               grind)
            | exact superpose b2e54 b2e17
            | (have j0 := b2e17 (σ y) X0
               grind)
            | (have r₁ := b2e17 (σ y) X0
               have r₂ := b2e54 X0
               grind)
            | exact resolve b2e17 b2e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e54
          have b2e75 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b2e71 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e71
          have b2e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X0 X1
               have i₂ := b2e18 (σ X0) (σ X1)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X1) (σ X1)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e111 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k X0 (τ X1))
               have i₂ := b2e30 X1 X0
               grind)
            | exact superpose b2e30 b2e14
            | exact resolve b2e14 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e173 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op X0 y) ∨ (k X1 (M.op X0 y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e16 X1 (M.op X0 y)
               have i₂ := b2e61 X0 (M.op X0 y)
               grind)
            | exact superpose b2e61 b2e16
            | (have j0 := b2e16 X1 (M.op X0 y)
               grind)
            | (have r₁ := b2e16 X0 (M.op X0 y)
               have r₂ := b2e61 X0 (M.op X0 y)
               grind)
            | exact resolve b2e16 b2e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e61
          have b2e180 : ∀ X0 X1 : G, (k X1 (M.op X0 y)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e173 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e173
          have b2e283 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X0))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e180 (M.op (M.op X0 X1) x) X2
               have i₂ := b2e51 X0 X1 x y
               grind)
            | exact superpose b2e51 b2e180
            | exact resolve b2e180 b2e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e51 b2e180
          have b2e1266 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b2e86 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e86
          have b2e1268 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b2e1266 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1266
          have b2e1535 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e111 X0 (M.op X1 (M.op X2 X1))
               have i₂ := b2e283 X1 X2 (σ X0)
               grind)
            | exact superpose b2e283 b2e111
            | exact resolve b2e111 b2e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e111 b2e283
          have b2e1565 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 X1)))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e1535 X0 X1 X2
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e1535
            | exact resolve b2e1535 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1535
          have b2e1714 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e45 X0 X0 X2 x
               have i₂ := b2e67 X0
               grind)
            | exact superpose b2e67 b2e45
            | (have j1 := b2e67 X0
               grind)
            | exact resolve b2e45 b2e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e2343 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e45 X0 X0 X2 x
               have i₂ := b2e75 X0
               grind)
            | exact superpose b2e75 b2e45
            | (have j1 := b2e75 X0
               grind)
            | exact resolve b2e45 b2e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e45
          have b2e2375 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e19 y X0
               have i₂ := b2e75 (σ X0)
               grind)
            | exact superpose b2e75 b2e19
            | (have j1 := b2e75 (σ X0)
               grind)
            | exact resolve b2e19 b2e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e75
          have b2e7640 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b2e1268 (τ X0)
               have i₂ := b2e30 X0 (τ X0)
               grind)
            | exact superpose b2e30 b2e1268
            | (have j0 := b2e1268 (τ X0)
               grind)
            | exact resolve b2e1268 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30 b2e1268
          have b2e7674 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b2e7640 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e7640
            | (have j0 := b2e7640 X0
               grind)
            | exact resolve b2e7640 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e7640
          have b2e7689 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e7674 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e7674
            | (have j0 := b2e7674 X0
               grind)
            | exact resolve b2e7674 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e7674
          have b2e210716 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x y) = (k y x) := by
            intro X0
            first
            | (have i₁ := b2e24
               have i₂ := b2e1714 x x X0
               grind)
            | (have i₁ := b2e24
               have i₂ := b2e1714 x X0 x
               grind)
            | exact superpose b2e1714 b2e24
            | (have j1 := b2e1714 x x x
               grind)
            | exact resolve b2e24 b2e1714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e210722 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e67 X0
               have i₂ := b2e1714 X0 X0 X1
               grind)
            | (have i₁ := b2e67 X0
               have i₂ := b2e1714 X0 X1 X0
               grind)
            | exact superpose b2e1714 b2e67
            | (have j0 := b2e67 X0
               have j1 := b2e1714 X0 X1 x
               grind)
            | exact resolve b2e67 b2e1714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e67 b2e1714
          have b2e211573 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have j0 := b2e210722 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e210722
          have b2e211614 : (M.op x y) = (k y x) := by
            first
            | (have j1 := b2e211573 x x
               grind)
            | (have r₁ := b2e210716 x
               have r₂ := b2e211573 x x
               grind)
            | exact resolve b2e210716 b2e211573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e210716 b2e211573
          have b2e239994 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b2e20
               have i₂ := b2e2343 (σ x) (σ y) X0
               grind)
            | (have i₁ := b2e20
               have i₂ := b2e2343 (σ x) X0 (σ y)
               grind)
            | exact superpose b2e2343 b2e20
            | (have j1 := b2e2343 (σ x) x x
               grind)
            | exact resolve b2e20 b2e2343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2343
          have b2e240149 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e239994 X0
               have i₂ := b2e19 y x
               grind)
            | exact superpose b2e19 b2e239994
            | (have j0 := b2e239994 X0
               grind)
            | exact resolve b2e239994 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e239994
          have b2e240187 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e240149 X0
               have i₂ := b2e211614
               grind)
            | exact superpose b2e211614 b2e240149
            | (have j0 := b2e240149 X0
               grind)
            | exact resolve b2e240149 b2e211614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e240149
          have b2e240208 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b2e240187 X0
               grind)
            | (have r₁ := b2e240187 X0
               have r₂ := b2e20
               grind)
            | exact resolve b2e240187 b2e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e240187
          have b2e293945 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e240208 (σ y)
               have i₂ := b2e2375 x
               grind)
            | exact superpose b2e2375 b2e240208
            | (have j1 := b2e2375 x
               grind)
            | exact resolve b2e240208 b2e2375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e2375 b2e240208
          have b2e294191 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e293945
               have i₂ := b2e211614
               grind)
            | exact superpose b2e211614 b2e293945
            | exact resolve b2e293945 b2e211614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e211614 b2e293945
          have b2e294192 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b2e294191
          have b2e294361 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ x)))) = X0 := by
            intro X0
            first
            | (have i₁ := b2e1565 X0 (σ x) (σ x)
               have i₂ := b2e294192
               grind)
            | exact superpose b2e294192 b2e1565
            | exact resolve b2e1565 b2e294192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1565
          have b2e294448 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b2e294361 X0
               have i₂ := b2e294192
               grind)
            | exact superpose b2e294192 b2e294361
            | exact resolve b2e294361 b2e294192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e294192 b2e294361
          have b2e294505 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b2e294448 X0
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e294448
            | exact resolve b2e294448 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e294448
          have b2e294692 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have i₁ := b2e7689 x
               have i₂ := b2e294505 x
               grind)
            | exact superpose b2e294505 b2e7689
            | (have j0 := b2e7689 x
               grind)
            | (have r₁ := b2e7689 x
               have r₂ := b2e294505 x
               grind)
            | exact resolve b2e7689 b2e294505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e7689 b2e294505
          have b2e294773 : x = (M.op x x) := by grind
          clear b2e294692
          have b2e294831 : False := by grind
          exact b2e294831
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e42 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e13 x x x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e47 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e42 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e42
            | exact resolve b3e42 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e42
          have b3e67 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e25
               have i₂ := b3e47 y
               grind)
            | exact superpose b3e47 b3e25
            | exact resolve b3e25 b3e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25 b3e47
          have b3e74 : False := by grind
          exact b3e74
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b4e25 : x ≠ (M.op x x) := by grind
            have b4e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : False := by grind
            exact b4e27
          · have b5e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op y y) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b5e17 X0 y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e17
              | (have j0 := b5e17 X0 y
                 grind)
              | (have r₁ := b5e17 X0 y
                 have r₂ := b5e22
                 grind)
              | exact resolve b5e17 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e29 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b5e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e28
            have b5e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b5e20 (τ X0) X1
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e20
              | exact resolve b5e20 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e33 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b5e30 X0 y
                 have i₂ := b5e29 (τ X0)
                 grind)
              | exact superpose b5e29 b5e30
              | exact resolve b5e30 b5e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29 b5e30
            have b5e37 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e33 X0
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e33
              | exact resolve b5e33 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e33
            have b5e85 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e23
                 have i₂ := b5e19 X0 (σ y)
                 grind)
              | exact superpose b5e19 b5e23
              | (have j1 := b5e19 X0 (σ y)
                 grind)
              | (have r₁ := b5e23
                 have r₂ := b5e19 X0 (σ y)
                 grind)
              | (have r₁ := b5e23
                 have r₂ := b5e19 (σ y) (σ y)
                 grind)
              | exact resolve b5e23 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e86 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b5e85 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e85
            have b5e92 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e86 X0
                 have i₂ := b5e37 X0
                 grind)
              | exact superpose b5e37 b5e86
              | (have j0 := b5e86 X0
                 grind)
              | exact resolve b5e86 b5e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e37 b5e86
            have b5e93 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b5e92 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e92
            have b5e102 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e93 (σ y)
                 grind)
              | exact superpose b5e93 b5e23
              | (have r₁ := b5e23
                 have r₂ := b5e93 (σ y)
                 grind)
              | exact resolve b5e23 b5e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e93
            have b5e103 : False := by grind
            exact b5e103
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e25 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 X0 y
               grind)
            | (have r₁ := b6e16 X0 y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e28 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b6e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e25
          have b6e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 (τ X0) X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e103 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e29 X0 y
               have i₂ := b6e28 (τ X0)
               grind)
            | exact superpose b6e28 b6e29
            | exact resolve b6e29 b6e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28 b6e29
          have b6e108 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e103 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e103
            | exact resolve b6e103 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e103
          have b6e113 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e18 X0 (σ y)
               have i₂ := b6e108 X0
               grind)
            | exact superpose b6e108 b6e18
            | (have j0 := b6e18 X0 (σ y)
               grind)
            | exact resolve b6e18 b6e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e108
          have b6e115 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have j0 := b6e113 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e113
          have b6e118 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b6e115 X0
               grind)
            | (have r₁ := b6e115 (σ y)
               have r₂ := b6e22
               grind)
            | (have r₁ := b6e115 X0
               have r₂ := b6e22
               grind)
            | exact resolve b6e115 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e115
          have b6e194 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e118 (σ x)
               grind)
            | exact superpose b6e118 b6e23
            | (have r₁ := b6e23
               have r₂ := b6e118 (σ x)
               grind)
            | exact resolve b6e23 b6e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e118
          have b6e195 : False := by grind
          exact b6e195
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b7e25 : x ≠ (M.op x x) := by grind
            have b7e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : False := by grind
            exact b7e27
          · have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op y y) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b8e17 X0 y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 X0 y
                 grind)
              | (have r₁ := b8e17 X0 y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e28 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b8e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e27
            have b8e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 (τ X0) X1
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e29 X0 y
                 have i₂ := b8e28 (τ X0)
                 grind)
              | exact superpose b8e28 b8e29
              | exact resolve b8e29 b8e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28 b8e29
            have b8e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e32 X0
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e32
              | exact resolve b8e32 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32
            have b8e77 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e23
                 have i₂ := b8e19 X0 (σ y)
                 grind)
              | exact superpose b8e19 b8e23
              | (have j1 := b8e19 X0 (σ y)
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e19 X0 (σ y)
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e19 (σ y) (σ y)
                 grind)
              | exact resolve b8e23 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e78 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b8e77 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e77
            have b8e84 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e78 X0
                 have i₂ := b8e36 X0
                 grind)
              | exact superpose b8e36 b8e78
              | (have j0 := b8e78 X0
                 grind)
              | exact resolve b8e78 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36 b8e78
            have b8e85 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b8e84 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e84
            have b8e96 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b8e24
                 have i₂ := b8e85 (σ x)
                 grind)
              | exact superpose b8e85 b8e24
              | (have r₁ := b8e24
                 have r₂ := b8e85 (σ x)
                 grind)
              | exact resolve b8e24 b8e85
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e85
            have b8e97 : False := by grind
            exact b8e97
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b9e16 X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 X0 (σ y)
               grind)
            | (have r₁ := b9e16 X0 (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b9e27 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e33 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 y
               have i₂ := b9e28 (σ X0)
               grind)
            | exact superpose b9e28 b9e19
            | exact resolve b9e19 b9e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e28
          have b9e95 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b9e14 (k X0 y)
               have i₂ := b9e33 X0
               grind)
            | exact superpose b9e33 b9e14
            | exact resolve b9e14 b9e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e33
          have b9e96 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b9e95 X0
               have i₂ := b9e14 X0
               grind)
            | exact superpose b9e14 b9e95
            | exact resolve b9e95 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e95
          have b9e119 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b9e18 X0 y
               have i₂ := b9e96 X0
               grind)
            | exact superpose b9e96 b9e18
            | (have j0 := b9e18 X0 y
               grind)
            | exact resolve b9e18 b9e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e96
          have b9e120 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
            intro X0
            first
            | (have j0 := b9e119 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e119
          have b9e122 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b9e120 X0
               grind)
            | (have r₁ := b9e120 y
               have r₂ := b9e21
               grind)
            | (have r₁ := b9e120 X0
               have r₂ := b9e21
               grind)
            | exact resolve b9e120 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e120
          have b9e140 : y ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e122 y
               grind)
            | exact superpose b9e122 b9e21
            | (have r₁ := b9e21
               have r₂ := b9e122 y
               grind)
            | exact resolve b9e21 b9e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e122
          have b9e147 : False := by grind
          exact b9e147
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b10e25 : x ≠ (M.op x x) := by grind
            have b10e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : False := by grind
            exact b10e27
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op y y) := by grind
            have b11e23 : x = (M.op x y) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            have b11e26 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b11e17 X0 (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 X0 (σ y)
                 grind)
              | (have r₁ := b11e17 X0 (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e29 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b11e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28
            have b11e33 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b11e29 (σ X0)
                 have i₂ := b11e20 X0 y
                 grind)
              | exact superpose b11e20 b11e29
              | exact resolve b11e29 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e36 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b11e15 (k X0 y)
                 have i₂ := b11e33 X0
                 grind)
              | exact superpose b11e33 b11e15
              | exact resolve b11e15 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33
            have b11e37 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b11e36 X0
                 have i₂ := b11e15 X0
                 grind)
              | exact superpose b11e15 b11e36
              | exact resolve b11e36 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e36
            have b11e57 : x ≠ x ∨ y = (M.op y y) ∨ (M.op y x) = (k x y) := by
              first
              | (have i₁ := b11e18 x y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x y
                 grind)
              | (have r₁ := b11e18 x y
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e58 : y = (M.op y y) ∨ (M.op y x) = (k x y) := by grind
            clear b11e57
            have b11e59 : (M.op y x) = (k x y) := by
              first
              | (have r₁ := b11e58
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e58 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e58
            have b11e61 : x = (M.op y x) := by
              first
              | (have i₁ := b11e59
                 have i₂ := b11e37 x
                 grind)
              | exact superpose b11e37 b11e59
              | exact resolve b11e59 b11e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e37 b11e59
            have b11e63 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b11e14 y x X0
                 have i₂ := b11e61
                 grind)
              | exact superpose b11e61 b11e14
              | exact resolve b11e14 b11e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e64 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b11e63 X0
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e63
              | exact resolve b11e63 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e63
            have b11e66 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b11e64 X0
                 have i₂ := b11e61
                 grind)
              | exact superpose b11e61 b11e64
              | exact resolve b11e64 b11e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e61 b11e64
            have b11e92 : x ≠ x := by
              first
              | (have i₁ := b11e26
                 have i₂ := b11e66 x
                 grind)
              | exact superpose b11e66 b11e26
              | (have r₁ := b11e26
                 have r₂ := b11e66 x
                 grind)
              | exact resolve b11e26 b11e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e66
            have b11e93 : False := by grind
            exact b11e93
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : x = (M.op x y) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e27 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e28 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e27
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e27
              | exact resolve b12e27 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e27
            have b12e29 : False := by grind
            exact b12e29
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b13e27 : x ≠ (M.op x x) := by grind
              have b13e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : False := by grind
              exact b13e29
            · have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : x = (M.op x y) := by grind
              have b14e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e22
                | exact resolve b14e22 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e30 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b14e29
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e29
                | exact resolve b14e29 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29
              have b14e31 : False := by grind
              exact b14e31
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e28 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e17 X0 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e17
              | (have j0 := b15e17 X0 x
                 grind)
              | (have r₁ := b15e17 X0 x
                 have r₂ := b15e26
                 grind)
              | exact resolve b15e17 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e29 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28
            have b15e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 X0 X1 X3
                 have i₂ := b15e14 X0 X1 X2
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X0 X1
                 have i₂ := b15e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X1) (σ X1)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e1500 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e75 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e75
            have b15e1502 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e1500 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1500
            have b15e8351 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e1502 x
                 have i₂ := b15e29 x
                 grind)
              | exact superpose b15e29 b15e1502
              | (have j0 := b15e1502 x
                 grind)
              | exact resolve b15e1502 b15e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e29 b15e1502
            have b15e8357 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b15e8351
            have b15e8419 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e41 (σ x) (σ x) x x
                 have i₂ := b15e8357
                 grind)
              | exact superpose b15e8357 b15e41
              | exact resolve b15e41 b15e8357
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e41
            have b15e10755 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e8357
                 have i₂ := b15e8419 X0 (σ x)
                 grind)
              | (have i₁ := b15e8357
                 have i₂ := b15e8419 (σ x) X0
                 grind)
              | exact superpose b15e8419 b15e8357
              | exact resolve b15e8357 b15e8419
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e8357
            have b15e10756 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e8419 X0 (σ y)
                 grind)
              | (have i₁ := b15e25
                 have i₂ := b15e8419 (σ y) X0
                 grind)
              | exact superpose b15e8419 b15e25
              | exact resolve b15e25 b15e8419
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e8419
            have b15e10771 : False := by grind
            exact b15e10771
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b16e27 : x ≠ (M.op x x) := by grind
              have b16e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : False := by grind
              exact b16e29
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b17e24 : x = (M.op x y) := by grind
              have b17e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e36 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e15 x y X0
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e43 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e36 X1
                   have i₂ := b17e36 X0
                   grind)
                | (have i₁ := b17e36 X0
                   have i₂ := b17e36 (M.op y x)
                   grind)
                | exact superpose b17e36 b17e36
                | exact resolve b17e36 b17e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36
              have b17e97 : ∀ X0 : G, x ≠ (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e28
                   have i₂ := b17e43 x X0
                   grind)
                | (have i₁ := b17e28
                   have i₂ := b17e43 X0 x
                   grind)
                | exact superpose b17e43 b17e28
                | exact resolve b17e28 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e98 : ∀ X0 : G, x = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e24
                   have i₂ := b17e43 y X0
                   grind)
                | (have i₁ := b17e24
                   have i₂ := b17e43 X0 y
                   grind)
                | exact superpose b17e43 b17e24
                | exact resolve b17e24 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e43
              have b17e99 : False := by grind
              exact b17e99
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b18e22 : x ≠ (M.op x y) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e42 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b18e13 x x x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e45 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b18e42 X0
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e42
            | exact resolve b18e42 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e42
          have b18e54 : x ≠ x := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e45 y
               grind)
            | exact superpose b18e45 b18e22
            | (have r₁ := b18e22
               have r₂ := b18e45 y
               grind)
            | exact resolve b18e22 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45
          have b18e55 : False := by grind
          exact b18e55
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b19e25 : x ≠ (M.op x x) := by grind
            have b19e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : False := by grind
            exact b19e27
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y y) := by grind
            have b20e23 : x ≠ (M.op x y) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 X0 (σ y)
                 grind)
              | (have r₁ := b20e17 X0 (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b20e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e27
            have b20e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 y
                 have i₂ := b20e28 (σ X0)
                 grind)
              | exact superpose b20e28 b20e20
              | exact resolve b20e20 b20e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e15 (k X0 y)
                 have i₂ := b20e32 X0
                 grind)
              | exact superpose b20e32 b20e15
              | exact resolve b20e15 b20e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e36 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e35 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e35
              | exact resolve b20e35 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e73 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e36 X0
                 have i₂ := b20e19 X0 y
                 grind)
              | exact superpose b20e19 b20e36
              | (have j1 := b20e19 X0 y
                 grind)
              | exact resolve b20e36 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e80 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
              intro X0
              first
              | (have j0 := b20e73 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e73
            have b20e85 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b20e80 X0
                 grind)
              | (have r₁ := b20e80 y
                 have r₂ := b20e22
                 grind)
              | (have r₁ := b20e80 X0
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e80 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e80
            have b20e89 : x ≠ x := by
              first
              | (have i₁ := b20e23
                 have i₂ := b20e85 x
                 grind)
              | exact superpose b20e85 b20e23
              | (have r₁ := b20e23
                 have r₂ := b20e85 x
                 grind)
              | exact resolve b20e23 b20e85
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e85
            have b20e96 : False := by grind
            exact b20e96
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b21e23 : x ≠ (M.op x y) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e41 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e14 x x x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e44 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e41 X0
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e41
              | exact resolve b21e41 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e41
            have b21e52 : x ≠ x := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e44 y
                 grind)
              | exact superpose b21e44 b21e23
              | (have r₁ := b21e23
                 have r₂ := b21e44 y
                 grind)
              | exact resolve b21e23 b21e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e44
            have b21e53 : False := by grind
            exact b21e53
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b22e27 : x ≠ (M.op x x) := by grind
              have b22e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : False := by grind
              exact b22e29
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              have b23e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X0 X1 X3
                   have i₂ := b23e15 X0 X1 X2
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e97 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e39 (σ x) (σ y) x x
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e39
                | exact resolve b23e39 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e39
              have b23e143 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e18 X1 (σ x)
                   have i₂ := b23e97 (σ x) X0
                   grind)
                | (have i₁ := b23e18 X1 (σ x)
                   have i₂ := b23e97 X0 (σ x)
                   grind)
                | exact superpose b23e97 b23e18
                | (have j0 := b23e18 X1 (σ x)
                   grind)
                | exact resolve b23e18 b23e97
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e149 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b23e26
                   have i₂ := b23e97 (σ y) X0
                   grind)
                | (have i₁ := b23e26
                   have i₂ := b23e97 X0 (σ y)
                   grind)
                | exact superpose b23e97 b23e26
                | exact resolve b23e26 b23e97
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e97
              have b23e154 : ∀ X1 : G, (k X1 (σ x)) = X1 := by
                intro X1
                first
                | (have j0 := b23e143 x X1
                   grind)
                | (have r₁ := b23e143 x X1
                   have r₂ := b23e149 x
                   grind)
                | exact resolve b23e143 b23e149
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e143 b23e149
              have b23e195 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 x
                   have i₂ := b23e154 (σ X0)
                   grind)
                | exact superpose b23e154 b23e21
                | exact resolve b23e21 b23e154
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e154
              have b23e362 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b23e16 (k X0 x)
                   have i₂ := b23e195 X0
                   grind)
                | exact superpose b23e195 b23e16
                | exact resolve b23e16 b23e195
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e195
              have b23e363 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e362 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e362
                | exact resolve b23e362 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e362
              have b23e435 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x x) ∨ (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e20 X0 x
                   have i₂ := b23e363 X0
                   grind)
                | exact superpose b23e363 b23e20
                | (have j0 := b23e20 X0 x
                   grind)
                | exact resolve b23e20 b23e363
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e363
              have b23e436 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x x) := by
                intro X0
                first
                | (have j0 := b23e435 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e435
              have b23e438 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have j0 := b23e436 X0
                   grind)
                | (have r₁ := b23e436 x
                   have r₂ := b23e28
                   grind)
                | (have r₁ := b23e436 X0
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e436 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e436
              have b23e659 : x ≠ x := by
                first
                | (have i₁ := b23e28
                   have i₂ := b23e438 x
                   grind)
                | exact superpose b23e438 b23e28
                | (have r₁ := b23e28
                   have r₂ := b23e438 x
                   grind)
                | exact resolve b23e28 b23e438
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e438
              have b23e677 : False := by grind
              exact b23e677
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b24e23 : x ≠ (M.op x y) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e36 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b24e14 x x x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e42 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b24e36 X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e36
              | exact resolve b24e36 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36
            have b24e48 : x ≠ x := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e42 y
                 grind)
              | exact superpose b24e42 b24e23
              | (have r₁ := b24e23
                 have r₂ := b24e42 y
                 grind)
              | exact resolve b24e23 b24e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e42
            have b24e49 : False := by grind
            exact b24e49
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b25e27 : x ≠ (M.op x x) := by grind
              have b25e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : False := by grind
              exact b25e29
            · have b26e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op y y) := by grind
              have b26e24 : x ≠ (M.op x y) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e74 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (σ y)
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ y) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e75 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have j0 := b26e74 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e74
              have b26e657 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 y
                   have i₂ := b26e75 (σ X0)
                   grind)
                | exact superpose b26e75 b26e21
                | (have j1 := b26e75 (σ X0)
                   grind)
                | exact resolve b26e21 b26e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e75
              have b26e29485 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e657 x
                   grind)
                | exact superpose b26e657 b26e22
                | (have j1 := b26e657 x
                   grind)
                | exact resolve b26e22 b26e657
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e657
              have b26e29607 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b26e29485
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e29485 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29485
              have b26e29612 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e29607
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e29607
                | (have j1 := b26e20 y y
                   grind)
                | exact resolve b26e29607 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29607
              have b26e29613 : y = (M.op y y) ∨ x = (M.op x y) := by grind
              clear b26e29612
              have b26e29616 : x = (M.op x y) := by
                first
                | (have r₁ := b26e29613
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e29613 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29613
              have b26e29619 : False := by grind
              exact b26e29619

/-- `Equation4445`: `x ◇ (y ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pyx_Equation4445 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4445 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4445.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e31 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e11 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e11 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
      have b0e36 : (M.op y x) = (k x y) := by grind
      have b0e37 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e35
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e35
        | exact resolve b0e35 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e38 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e37
           have i₂ := b0e36
           grind)
        | exact superpose b0e36 b0e37
        | exact resolve b0e37 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e37
      have b0e92 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e31
           grind)
        | exact superpose b0e31 b0e18
        | exact resolve b0e18 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e93 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e92
           have i₂ := b0e38
           grind)
        | exact superpose b0e38 b0e92
        | exact resolve b0e92 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e92
      have b0e94 : (σ (M.op y x)) ≠ (σ (M.op y x)) := by
        first
        | (have i₁ := b0e93
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e93
        | exact resolve b0e93 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e93
      have b0e95 : False := by grind
      exact b0e95
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b1e30 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e12 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e34 : (M.op y x) = (k x y) := by grind
        have b1e35 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e33
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e33
          | exact resolve b1e33 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e36 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e42 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e36
             have r₂ := b1e21
             grind)
          | exact resolve b1e36 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e43 : (σ x) = (σ (k x y)) := by
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
        have b1e44 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e34
             grind)
          | exact superpose b1e34 b1e43
          | exact resolve b1e43 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e43
        have b1e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e68 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b1e74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e17 (σ X1) (σ X0)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X0)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e76 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e99 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e19
          | exact resolve b1e19 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e100 : (σ (k y x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e99
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e99
          | exact resolve b1e99 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e101 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e100
             have i₂ := b1e44
             grind)
          | exact superpose b1e44 b1e100
          | exact resolve b1e100 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e100
        have b1e176 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        clear b1e76
        have b1e317 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        clear b1e75
        have b1e330 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e317 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e317
        have b1e343 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e101
             have i₂ := b1e330 y x
             grind)
          | exact superpose b1e330 b1e101
          | (have j1 := b1e330 y x
             grind)
          | exact resolve b1e101 b1e330
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e330
        have b1e346 : (σ x) ≠ (σ (M.op y x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e343
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e343
          | exact resolve b1e343 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e343
        have b1e349 : y = (k y x) := by
          first
          | (have r₁ := b1e346
             have r₂ := b1e44
             grind)
          | exact resolve b1e346 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e346
        have b1e403 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e101
             have i₂ := b1e349
             grind)
          | exact superpose b1e349 b1e101
          | exact resolve b1e101 b1e349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e954 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e176 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e176
        have b1e955 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e954 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e954
        have b1e977 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e74 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e74
          | exact resolve b1e74 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e1185 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b1e977
        have b1e1226 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b1e1185
             have r₂ := b1e403
             grind)
          | exact resolve b1e1185 b1e403
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1185
        have b1e1247 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e1226
             have i₂ := b1e955 x
             grind)
          | exact superpose b1e955 b1e1226
          | exact resolve b1e1226 b1e955
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e955 b1e1226
        have b1e1255 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op x x)
             have i₂ := b1e1247
             grind)
          | exact superpose b1e1247 b1e13
          | exact resolve b1e13 b1e1247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1247
        have b1e1272 : y = (M.op x x) := by
          first
          | (have i₁ := b1e1255
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e1255
          | exact resolve b1e1255 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1255
        have b1e1438 : (M.op x y) = (k y x) := by grind
        clear b1e1272
        have b1e1446 : y = (M.op x y) := by
          first
          | (have i₁ := b1e1438
             have i₂ := b1e349
             grind)
          | exact superpose b1e349 b1e1438
          | exact resolve b1e1438 b1e349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e349 b1e1438
        have b1e1654 : y = (M.op y x) := by
          first
          | (have i₁ := b1e30
             have i₂ := b1e1446
             grind)
          | exact superpose b1e1446 b1e30
          | exact resolve b1e30 b1e1446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e1446
        have b1e1880 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e1654
             grind)
          | exact superpose b1e1654 b1e44
          | exact resolve b1e44 b1e1654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e1654
        have b1e1889 : False := by grind
        exact b1e1889
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e66 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        clear b2e66
        have b2e1425 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e101 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e101
        have b2e1426 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e1425 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1425
        have b2e1464 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e1426 (σ X0)
             grind)
          | exact superpose b2e1426 b2e18
          | exact resolve b2e18 b2e1426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1471 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1464 X0
             have i₂ := b2e1426 X0
             grind)
          | exact superpose b2e1426 b2e1464
          | exact resolve b2e1464 b2e1426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1426 b2e1464
        have b2e1735 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1471 y
             grind)
          | exact superpose b2e1471 b2e21
          | exact resolve b2e21 b2e1471
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1471
        have b2e1789 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1735
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1735
          | exact resolve b2e1735 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1735
        have b2e1790 : False := by grind
        exact b2e1790
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b3e29 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e12 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e12 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b3e34 : (M.op x y) = (k y x) := by grind
        have b3e35 : (M.op y x) = (k y x) := by
          first
          | (have i₁ := b3e34
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e34
          | exact resolve b3e34 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e36 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e33
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e33
          | exact resolve b3e33 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e37 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        have b3e38 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e43 : x = (k x y) := by
          first
          | (have r₁ := b3e38
             have r₂ := b3e20
             grind)
          | exact resolve b3e38 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e44 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e37
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e37
          | exact resolve b3e37 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e45 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e44
          | exact resolve b3e44 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e64 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b3e69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b3e72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e98 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e29
             grind)
          | exact superpose b3e29 b3e19
          | exact resolve b3e19 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e99 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e98
             have i₂ := b3e36
             grind)
          | exact superpose b3e36 b3e98
          | exact resolve b3e98 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98
        have b3e100 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e99
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e99
          | exact resolve b3e99 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e101 : (σ x) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b3e100
             have i₂ := b3e30
             grind)
          | exact superpose b3e30 b3e100
          | exact resolve b3e100 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e100
        have b3e176 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op y x)) := by grind
        clear b3e45
        have b3e178 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e176
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e176
          | exact resolve b3e176 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e176
        have b3e179 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e178
             have i₂ := b3e35
             grind)
          | exact superpose b3e35 b3e178
          | exact resolve b3e178 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e178
        have b3e180 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e179
             have i₂ := b3e29
             grind)
          | exact superpose b3e29 b3e179
          | exact resolve b3e179 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e179
        have b3e181 : (σ (k x y)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e180
             have i₂ := b3e36
             grind)
          | exact superpose b3e36 b3e180
          | exact resolve b3e180 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e180
        have b3e182 : (σ x) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e181
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e181
          | exact resolve b3e181 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e181
        have b3e183 : (σ y) = (σ (M.op y x)) := by
          first
          | (have r₁ := b3e182
             have r₂ := b3e101
             grind)
          | exact resolve b3e182 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e182
        have b3e184 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e101
             have i₂ := b3e183
             grind)
          | exact superpose b3e183 b3e101
          | exact resolve b3e101 b3e183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101 b3e183
        have b3e322 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        clear b3e72
        have b3e335 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e322 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e322
        have b3e971 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e69 y y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e69
          | exact resolve b3e69 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e1183 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b3e971
        have b3e1207 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b3e1183
             have r₂ := b3e184
             grind)
          | exact resolve b3e1183 b3e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1183
        have b3e1226 : (k y y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e1207
             grind)
          | exact superpose b3e1207 b3e13
          | exact resolve b3e13 b3e1207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1207
        have b3e1240 : x = (k y y) := by
          first
          | (have i₁ := b3e1226
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1226
          | exact resolve b3e1226 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1226
        have b3e1416 : x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b3e335 y y
             have i₂ := b3e1240
             grind)
          | exact superpose b3e1240 b3e335
          | exact resolve b3e335 b3e1240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e335 b3e1240
        have b3e1421 : x = y := by
          first
          | (have r₁ := b3e1416
             have r₂ := b3e20
             grind)
          | exact resolve b3e1416 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1416
        have b3e1638 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e184
             have i₂ := b3e1421
             grind)
          | exact superpose b3e1421 b3e184
          | exact resolve b3e184 b3e1421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e184 b3e1421
        have b3e1645 : False := by grind
        exact b3e1645
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e40 : (M.op x y) = (k y x) := by grind
          have b4e41 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e39
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e39
            | exact resolve b4e39 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e42 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e41
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e41
            | exact resolve b4e41 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e41
          have b4e43 : False := by grind
          exact b4e43
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e37 : (M.op x y) = (k y x) := by grind
          have b5e54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e116 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e70 (σ y) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e70 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b5e70 b5e23
            | (have j1 := b5e70 (σ y) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e70 (σ y) (σ x)
               grind)
            | exact resolve b5e23 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e213 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e116 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116
          have b5e214 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e213
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e213
            | exact resolve b5e213 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213
          have b5e215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e214
               have i₂ := b5e37
               grind)
            | exact superpose b5e37 b5e214
            | exact resolve b5e214 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e214
          have b5e216 : False := by grind
          exact b5e216
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e63 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e77 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e122 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        clear b6e77
        have b6e591 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e122 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e122
        have b6e592 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e591 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e591
        have b6e643 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e592 (σ X0)
             grind)
          | exact superpose b6e592 b6e18
          | exact resolve b6e18 b6e592
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e650 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e643 X0
             have i₂ := b6e592 X0
             grind)
          | exact superpose b6e592 b6e643
          | exact resolve b6e643 b6e592
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e592 b6e643
        have b6e963 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e650 y
             grind)
          | exact superpose b6e650 b6e22
          | exact resolve b6e22 b6e650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e650
        have b6e1427 : (M.op y y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e963
             grind)
          | exact superpose b6e963 b6e13
          | exact resolve b6e13 b6e963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e963
        have b6e1446 : x = (M.op y y) := by
          first
          | (have i₁ := b6e1427
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1427
          | exact resolve b6e1427 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1427
        have b6e1451 : False := by grind
        exact b6e1451
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ (M.op y y) := by grind
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
          have b7e73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e143 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e90 y x
               grind)
            | exact superpose b7e90 b7e48
            | (have j1 := b7e90 y x
               grind)
            | exact resolve b7e48 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e90
          have b7e146 : x = (M.op y y) := by grind
          clear b7e143
          have b7e148 : False := by grind
          exact b7e148
        · have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e129 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e96 (σ y) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e96 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e96 b8e23
            | (have j1 := b8e96 (σ y) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e96 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e131 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e129 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e132 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e131
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e131
            | exact resolve b8e131 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e157 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e132
               grind)
            | exact superpose b8e132 b8e20
            | exact resolve b8e20 b8e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e157
               have i₂ := b8e96 y x
               grind)
            | exact superpose b8e96 b8e157
            | (have j1 := b8e96 y x
               grind)
            | exact resolve b8e157 b8e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e96 b8e157
          have b8e191 : x = (M.op y y) := by grind
          clear b8e188
          have b8e193 : False := by grind
          exact b8e193

/-- `Equation4456`: `x ◇ (y ◇ x) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxy_pxx_pxy_Equation4456 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4456 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4456.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (x) (x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          grind
        have b0e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          grind
        clear b0e30
        have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
        clear b0e31
        have b0e68 : False := by grind
        exact b0e68
      · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
        · have b1e21 : x = y := by grind
          have b1e23 : x ≠ x := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e30 : False := by grind
          exact b1e30
        · have b2e21 : x = y := by grind
          have b2e23 : x ≠ x := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : False := by grind
          exact b2e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (x) (x) with h2a | h2a
        · have b3e21 : x = y := by grind
          have b3e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e30 : False := by grind
          exact b3e30
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b4e22 : x = y := by grind
            have b4e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e33 : False := by grind
            exact b4e33
          · have b5e22 : x = y := by grind
            have b5e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e33 : False := by grind
            exact b5e33
      · rcases eq_or_ne (x) (x) with h2a | h2a
        · have b6e21 : x = y := by grind
          have b6e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e30 : False := by grind
          exact b6e30
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b7e22 : x = y := by grind
            have b7e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e33 : False := by grind
            exact b7e33
          · have b8e22 : x = y := by grind
            have b8e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e33 : False := by grind
            exact b8e33
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (x) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e21 : x ≠ y := by grind
          have b9e23 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e27 : y = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 y
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e14
            | exact resolve b9e14 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e28 : x = y := by
            first
            | (have i₁ := b9e27
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e27
            | exact resolve b9e27 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e29 : False := by grind
          exact b9e29
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b10e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : False := by grind
            exact b10e28
          · have b11e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : False := by grind
            exact b11e28
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (x) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : y = (M.op y x) := by grind
            have b12e25 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 X0 (M.op X2 X1) X3
                 have i₂ := b12e14 X0 X1 X2
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e36 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
              intro X0
              first
              | (have i₁ := b12e14 (σ x) (σ y) X0
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e39 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e14 X2 X0 (M.op x X1)
                 have i₂ := b12e14 X0 X1 x
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 (σ x) (σ y)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e41 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 x y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e42 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
              first
              | (have i₁ := b12e41 (M.op x x)
                 have i₂ := b12e41 x
                 grind)
              | exact superpose b12e41 b12e41
              | exact resolve b12e41 b12e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e44 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 x X1
                 have i₂ := b12e41 X0
                 grind)
              | exact superpose b12e41 b12e14
              | exact resolve b12e14 b12e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e45 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X1 (M.op x X0) X0
                 have i₂ := b12e41 X0
                 grind)
              | exact superpose b12e41 b12e14
              | exact resolve b12e14 b12e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e41
            have b12e47 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
              first
              | (have i₁ := b12e42
                 have i₂ := b12e44 (M.op y x) x
                 grind)
              | exact superpose b12e44 b12e42
              | exact resolve b12e42 b12e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e42
            have b12e48 : (M.op y (M.op x x)) = (M.op y y) := by
              first
              | (have i₁ := b12e47
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e47
              | exact resolve b12e47 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e47
            have b12e84 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 (M.op x x) y
                 have i₂ := b12e48
                 grind)
              | exact superpose b12e48 b12e14
              | exact resolve b12e14 b12e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e48
            have b12e87 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b12e84 X0
                 have i₂ := b12e45 x X0
                 grind)
              | exact superpose b12e45 b12e84
              | exact resolve b12e84 b12e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e45 b12e84
            have b12e90 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b12e87 X0
                 have i₂ := b12e44 X0 y
                 grind)
              | exact superpose b12e44 b12e87
              | exact resolve b12e87 b12e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e44 b12e87
            have b12e108 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
              intro X0
              first
              | (have i₁ := b12e14 X0 y y
                 have i₂ := b12e90 X0
                 grind)
              | exact superpose b12e90 b12e14
              | exact resolve b12e14 b12e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e90
            have b12e120 : y = (M.op x y) := by
              first
              | (have i₁ := b12e108 x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e108
              | exact resolve b12e108 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e108
            have b12e434 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (σ x) X1))) = (M.op (M.op X0 (σ y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e35 X1 (σ x) (σ y) X0
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e35
              | exact resolve b12e35 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e492 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b12e39 X1 x X0
                 have i₂ := b12e35 X0 X1 x X1
                 grind)
              | exact superpose b12e35 b12e39
              | exact resolve b12e39 b12e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e35 b12e39
            have b12e555 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X1)) = (M.op (M.op X0 (σ y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e434 X0 X1
                 have i₂ := b12e492 X1 (σ x)
                 grind)
              | exact superpose b12e492 b12e434
              | exact resolve b12e434 b12e492
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e434 b12e492
            have b12e585 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (σ y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e555 X0 X1
                 have i₂ := b12e40 X1
                 grind)
              | exact superpose b12e40 b12e555
              | exact resolve b12e555 b12e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40 b12e555
            have b12e1571 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b12e36 x
                 have i₂ := b12e585 x (σ x)
                 grind)
              | exact superpose b12e585 b12e36
              | exact resolve b12e36 b12e585
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e36 b12e585
            have b12e1611 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e1571
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e1571
              | exact resolve b12e1571 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1571
            have b12e1623 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e1611
                 grind)
              | exact superpose b12e1611 b12e21
              | exact resolve b12e21 b12e1611
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1611
            have b12e1641 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b12e1623
                 have i₂ := b12e120
                 grind)
              | exact superpose b12e120 b12e1623
              | exact resolve b12e1623 b12e120
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e120 b12e1623
            have b12e1642 : False := by grind
            exact b12e1642
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b13e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : False := by grind
              exact b13e30
            · have b14e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : False := by grind
              exact b14e30
        · rcases eq_or_ne (x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              grind
            have b15e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : x ≠ y := by grind
            have b15e23 : y = (M.op y x) := by grind
            have b15e24 : (σ x) ≠ (σ y) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              grind
            have b15e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              grind
            clear b15e31
            have b15e37 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 x y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e40 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
              first
              | (have i₁ := b15e37 (M.op x x)
                 have i₂ := b15e37 x
                 grind)
              | exact superpose b15e37 b15e37
              | exact resolve b15e37 b15e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e42 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 x X1
                 have i₂ := b15e37 X0
                 grind)
              | exact superpose b15e37 b15e14
              | exact resolve b15e14 b15e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e43 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 (M.op x X0) X0
                 have i₂ := b15e37 X0
                 grind)
              | exact superpose b15e37 b15e14
              | exact resolve b15e14 b15e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e45 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
              first
              | (have i₁ := b15e40
                 have i₂ := b15e42 (M.op y x) x
                 grind)
              | exact superpose b15e42 b15e40
              | exact resolve b15e40 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e40
            have b15e46 : (M.op y (M.op x x)) = (M.op y y) := by
              first
              | (have i₁ := b15e45
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e45
              | exact resolve b15e45 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e45
            have b15e47 : y ≠ y ∨ x = y ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b15e18 x y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e18
              | (have j0 := b15e18 x y
                 grind)
              | (have r₁ := b15e18 x y
                 have r₂ := b15e23
                 grind)
              | exact resolve b15e18 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e51 : x = y ∨ (M.op x x) = (k x y) := by grind
            clear b15e47
            have b15e52 : (M.op x x) = (k x y) := by
              first
              | (have r₁ := b15e51
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e51 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e51
            have b15e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
            have b15e66 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 (M.op X1 x))) = (M.op (M.op X2 X0) (M.op X1 x)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 (M.op X1 x) X0 X2
                 have i₂ := b15e42 (M.op X0 (M.op X1 x)) X1
                 grind)
              | exact superpose b15e42 b15e14
              | exact resolve b15e14 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e67 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op y (M.op x (M.op X0 x))) := by
              intro X0
              first
              | (have i₁ := b15e37 (M.op X0 x)
                 have i₂ := b15e42 (M.op x (M.op X0 x)) X0
                 grind)
              | exact superpose b15e42 b15e37
              | exact resolve b15e37 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37
            have b15e77 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 (M.op x x) y
                 have i₂ := b15e46
                 grind)
              | exact superpose b15e46 b15e14
              | exact resolve b15e14 b15e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e80 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b15e77 X0
                 have i₂ := b15e43 x X0
                 grind)
              | exact superpose b15e43 b15e77
              | exact resolve b15e77 b15e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e43 b15e77
            have b15e83 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b15e80 X0
                 have i₂ := b15e42 X0 y
                 grind)
              | exact superpose b15e42 b15e80
              | exact resolve b15e80 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e80
            have b15e101 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
              intro X0
              first
              | (have i₁ := b15e14 X0 y y
                 have i₂ := b15e83 X0
                 grind)
              | exact superpose b15e83 b15e14
              | exact resolve b15e14 b15e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e83
            have b15e113 : y = (M.op x y) := by
              first
              | (have i₁ := b15e101 x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e101
              | exact resolve b15e101 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e120 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 y) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 y X1
                 have i₂ := b15e101 X0
                 grind)
              | exact superpose b15e101 b15e14
              | exact resolve b15e14 b15e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e298 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 (M.op X1 y))) = (M.op (M.op X2 X0) (M.op X1 y)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 (M.op X1 y) X0 X2
                 have i₂ := b15e120 (M.op X0 (M.op X1 y)) X1
                 grind)
              | exact superpose b15e120 b15e14
              | exact resolve b15e14 b15e120
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e300 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y (M.op y (M.op X0 y))) := by
              intro X0
              first
              | (have i₁ := b15e101 (M.op X0 y)
                 have i₂ := b15e120 (M.op y (M.op X0 y)) X0
                 grind)
              | exact superpose b15e120 b15e101
              | exact resolve b15e101 b15e120
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e101 b15e120
            have b15e1012 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e55 y x
                 grind)
              | exact superpose b15e55 b15e25
              | (have j1 := b15e55 y x
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e55 x y
                 grind)
              | exact resolve b15e25 b15e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e1029 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e55 x y
                 grind)
              | exact superpose b15e55 b15e25
              | (have j1 := b15e55 x y
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e55 x y
                 grind)
              | exact resolve b15e25 b15e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e55
            have b15e1049 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
            clear b15e1029
            have b15e1056 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b15e1049
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e1049 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1049
            have b15e1060 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b15e1012
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e1012 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1012
            have b15e1070 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b15e1056
                 have i₂ := b15e52
                 grind)
              | exact superpose b15e52 b15e1056
              | exact resolve b15e1056 b15e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e52 b15e1056
            have b15e16158 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
              first
              | (have i₁ := b15e1060
                 have i₂ := b15e19 y x
                 grind)
              | exact superpose b15e19 b15e1060
              | (have j1 := b15e19 y x
                 grind)
              | (have r₁ := b15e1060
                 have r₂ := b15e19 (σ y) (σ (k y x))
                 grind)
              | (have r₁ := b15e1060
                 have r₂ := b15e19 (σ (k y x)) (σ y)
                 grind)
              | exact resolve b15e1060 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1060
            have b15e16159 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
              first
              | (have r₁ := b15e16158
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e16158 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16158
            have b15e16160 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b15e16159
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e16159
              | exact resolve b15e16159 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16159
            have b15e16161 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
            clear b15e16160
            have b15e16162 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b15e16161
                 have i₂ := b15e1070
                 grind)
              | exact superpose b15e1070 b15e16161
              | exact resolve b15e16161 b15e1070
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1070 b15e16161
            have b15e16163 : x = y ∨ (σ x) = (σ (M.op x x)) := by
              first
              | (have i₁ := b15e16162
                 have i₂ := b15e113
                 grind)
              | exact superpose b15e113 b15e16162
              | exact resolve b15e16162 b15e113
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16162
            have b15e16164 : (σ x) = (σ (M.op x x)) := by
              first
              | (have r₁ := b15e16163
                 have r₂ := b15e22
                 grind)
              | exact resolve b15e16163 b15e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16163
            have b15e16172 : (M.op x x) = (τ (σ x)) := by
              first
              | (have i₁ := b15e15 (M.op x x)
                 have i₂ := b15e16164
                 grind)
              | exact superpose b15e16164 b15e15
              | exact resolve b15e15 b15e16164
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e16175 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e32 (M.op x x)
                 have i₂ := b15e16164
                 grind)
              | exact superpose b15e16164 b15e32
              | exact resolve b15e32 b15e16164
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e16206 : (σ (M.op x x)) = (σ (M.op (M.op x x) (M.op x x))) := by
              first
              | (have i₁ := b15e16175
                 have i₂ := b15e32 x
                 grind)
              | exact superpose b15e32 b15e16175
              | exact resolve b15e16175 b15e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16175
            have b15e16209 : x = (M.op x x) := by
              first
              | (have i₁ := b15e16172
                 have i₂ := b15e15 x
                 grind)
              | exact superpose b15e15 b15e16172
              | exact resolve b15e16172 b15e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16172
            have b15e16211 : (σ (M.op x x)) = (σ (M.op y (M.op x (M.op x x)))) := by
              first
              | (have i₁ := b15e16206
                 have i₂ := b15e66 x x x
                 grind)
              | exact superpose b15e66 b15e16206
              | exact resolve b15e16206 b15e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e66 b15e16206
            have b15e16213 : (σ (M.op x x)) = (σ (M.op y (M.op x x))) := by
              first
              | (have i₁ := b15e16211
                 have i₂ := b15e67 x
                 grind)
              | exact superpose b15e67 b15e16211
              | exact resolve b15e16211 b15e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e67 b15e16211
            have b15e16215 : (σ (M.op x x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b15e16213
                 have i₂ := b15e46
                 grind)
              | exact superpose b15e46 b15e16213
              | exact resolve b15e16213 b15e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e46 b15e16213
            have b15e16217 : (σ x) = (σ (M.op y y)) := by
              first
              | (have i₁ := b15e16215
                 have i₂ := b15e16164
                 grind)
              | exact superpose b15e16164 b15e16215
              | exact resolve b15e16215 b15e16164
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16215
            have b15e16812 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b15e42 X0 x
                 have i₂ := b15e16209
                 grind)
              | exact superpose b15e16209 b15e42
              | exact resolve b15e42 b15e16209
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e42 b15e16209
            have b15e17852 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e32 (M.op y y)
                 have i₂ := b15e16217
                 grind)
              | exact superpose b15e16217 b15e32
              | exact resolve b15e32 b15e16217
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16217
            have b15e17891 : (σ (M.op x x)) = (σ (M.op (M.op y y) (M.op y y))) := by
              first
              | (have i₁ := b15e17852
                 have i₂ := b15e32 x
                 grind)
              | exact superpose b15e32 b15e17852
              | exact resolve b15e17852 b15e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e32 b15e17852
            have b15e17914 : (σ (M.op x x)) = (σ (M.op y (M.op y (M.op y y)))) := by
              first
              | (have i₁ := b15e17891
                 have i₂ := b15e298 y y y
                 grind)
              | exact superpose b15e298 b15e17891
              | exact resolve b15e17891 b15e298
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e298 b15e17891
            have b15e17931 : (σ (M.op x x)) = (σ (M.op y (M.op y y))) := by
              first
              | (have i₁ := b15e17914
                 have i₂ := b15e300 y
                 grind)
              | exact superpose b15e300 b15e17914
              | exact resolve b15e17914 b15e300
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e300 b15e17914
            have b15e17935 : (σ (M.op x x)) = (σ (M.op x (M.op y y))) := by
              first
              | (have i₁ := b15e17931
                 have i₂ := b15e16812 (M.op y y)
                 grind)
              | exact superpose b15e16812 b15e17931
              | exact resolve b15e17931 b15e16812
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e17931
            have b15e17937 : (σ (M.op x x)) = (σ (M.op x (M.op x y))) := by
              first
              | (have i₁ := b15e17935
                 have i₂ := b15e16812 y
                 grind)
              | exact superpose b15e16812 b15e17935
              | exact resolve b15e17935 b15e16812
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16812 b15e17935
            have b15e17939 : (σ (M.op x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b15e17937
                 have i₂ := b15e113
                 grind)
              | exact superpose b15e113 b15e17937
              | exact resolve b15e17937 b15e113
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e17937
            have b15e17941 : (σ (M.op x y)) = (σ x) := by
              first
              | (have i₁ := b15e17939
                 have i₂ := b15e16164
                 grind)
              | exact superpose b15e16164 b15e17939
              | exact resolve b15e17939 b15e16164
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16164 b15e17939
            have b15e17943 : (σ x) = (σ y) := by
              first
              | (have i₁ := b15e17941
                 have i₂ := b15e113
                 grind)
              | exact superpose b15e113 b15e17941
              | exact resolve b15e17941 b15e113
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e113 b15e17941
            have b15e17945 : False := by grind
            exact b15e17945
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b16e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : False := by grind
              exact b16e30
            · have b17e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e30 : False := by grind
              exact b17e30
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (x) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e21 : x ≠ y := by grind
          have b18e23 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e27 : y = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 y
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e14
            | exact resolve b18e14 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : x = y := by
            first
            | (have i₁ := b18e27
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e27
            | exact resolve b18e27 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e27
          have b18e29 : False := by grind
          exact b18e29
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b19e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : False := by grind
            exact b19e28
          · have b20e25 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : False := by grind
            exact b20e28
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b21e22 : x ≠ y := by grind
            have b21e23 : y ≠ (M.op y x) := by grind
            have b21e24 : (σ x) ≠ (σ y) := by grind
            have b21e25 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
              intro X0
              grind
            have b21e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              grind
            clear b21e31
            have b21e34 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
              intro X0
              first
              | (have i₁ := b21e14 (σ x) (σ y) X0
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 (M.op X1 X2) X2 X3
                 have i₂ := b21e14 X2 X1 X0
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X0 (M.op X2 X1) X3
                 have i₂ := b21e14 X0 X1 X2
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X2 X1 X3
                 have i₂ := b21e14 X2 X1 X0
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e38 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e39 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X3 (M.op X1 X2) X2
                 have i₂ := b21e14 X2 X1 X0
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e40 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 X2 X0 (M.op x X1)
                 have i₂ := b21e14 X0 X1 x
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b21e18 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e18
              | (have j0 := b21e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b21e18 (σ x) (σ y)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e18 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e51 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b21e48
            have b21e52 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
              first
              | (have r₁ := b21e51
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e51 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e51
            have b21e53 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b21e52
                 have i₂ := b21e32 x
                 grind)
              | exact superpose b21e32 b21e52
              | exact resolve b21e52 b21e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e52
            have b21e54 : (σ (M.op x x)) = (σ (k x y)) := by
              first
              | (have i₁ := b21e53
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e53
              | exact resolve b21e53 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e53
            have b21e57 : (k x y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e54
                 grind)
              | exact superpose b21e54 b21e15
              | exact resolve b21e15 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e58 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b21e57
                 have i₂ := b21e15 (M.op x x)
                 grind)
              | exact superpose b21e15 b21e57
              | exact resolve b21e57 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e57
            have b21e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e20 X0 X1
                 have i₂ := b21e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b21e19 b21e20
              | (have j1 := b21e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b21e20 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e64 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op y x) ∨ x = y := by
              first
              | (have i₁ := b21e54
                 have i₂ := b21e19 x y
                 grind)
              | exact superpose b21e19 b21e54
              | (have j1 := b21e19 x y
                 grind)
              | exact resolve b21e54 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e54
            have b21e65 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
              first
              | (have r₁ := b21e64
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e64 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e64
            have b21e66 : (σ (M.op x y)) = (σ (M.op x x)) := by
              first
              | (have r₁ := b21e65
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e65 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e65
            have b21e68 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = y := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e58
                 grind)
              | exact superpose b21e58 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e58
            have b21e69 : (M.op x y) = (M.op x x) ∨ x = y := by
              first
              | (have r₁ := b21e68
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e68 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e68
            have b21e71 : (M.op x y) = (M.op x x) := by
              first
              | (have r₁ := b21e69
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e69 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e69
            have b21e118 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e37 X0 (σ x) X1 (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e37
              | exact resolve b21e37 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e119 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e37 X1 (σ X0) X2 (σ X0)
                 have i₂ := b21e32 X0
                 grind)
              | exact superpose b21e32 b21e37
              | exact resolve b21e37 b21e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e152 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
              first
              | (have i₁ := b21e38 (σ x)
                 have i₂ := b21e32 x
                 grind)
              | exact superpose b21e32 b21e38
              | exact resolve b21e38 b21e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e162 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op (M.op (σ x) X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 (M.op (σ x) X0) X0
                 have i₂ := b21e38 X0
                 grind)
              | exact superpose b21e38 b21e14
              | exact resolve b21e14 b21e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e38
            have b21e168 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
              first
              | (have i₁ := b21e152
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e152
              | exact resolve b21e152 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e152
            have b21e291 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ (M.op x x)) X0)) := by
              intro X0
              first
              | (have i₁ := b21e14 X0 (σ (M.op x x)) (σ x)
                 have i₂ := b21e168
                 grind)
              | exact superpose b21e168 b21e14
              | exact resolve b21e14 b21e168
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e294 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (σ (M.op x x))) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e37 X0 (σ (M.op x x)) X1 (σ x)
                 have i₂ := b21e168
                 grind)
              | exact superpose b21e168 b21e37
              | exact resolve b21e37 b21e168
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e37
            have b21e311 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op X1 (M.op X1 (M.op (σ (M.op x x)) X1))) := by
              intro X0 X1
              first
              | (have i₁ := b21e36 X1 (σ (M.op x x)) (σ x) X0
                 have i₂ := b21e168
                 grind)
              | exact superpose b21e168 b21e36
              | exact resolve b21e36 b21e168
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e347 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b21e40 X1 x X0
                 have i₂ := b21e36 X0 X1 x X1
                 grind)
              | exact superpose b21e36 b21e40
              | exact resolve b21e40 b21e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e36 b21e40
            have b21e387 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op X1 (M.op (σ (M.op x x)) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b21e311 X0 X1
                 have i₂ := b21e347 X1 (σ (M.op x x))
                 grind)
              | exact superpose b21e347 b21e311
              | exact resolve b21e311 b21e347
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e311 b21e347
            have b21e401 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op X0 (σ y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b21e387 X0 X1
                 have i₂ := b21e291 X1
                 grind)
              | exact superpose b21e291 b21e387
              | exact resolve b21e387 b21e291
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e291 b21e387
            have b21e439 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 (M.op X1 (σ y))) (σ x)) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e39 X2 (M.op X1 (σ y)) (σ x) X0
                 have i₂ := b21e34 X1
                 grind)
              | exact superpose b21e34 b21e39
              | exact resolve b21e39 b21e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e442 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b21e39 X1 (σ y) (σ x) X0
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e39
              | exact resolve b21e39 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e39
            have b21e559 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
              intro X0
              first
              | (have i₁ := b21e442 X0 x
                 have i₂ := b21e119 x (M.op x (σ y)) X0
                 grind)
              | exact superpose b21e119 b21e442
              | exact resolve b21e442 b21e119
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e442
            have b21e562 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (M.op (M.op X2 (M.op X1 (σ y))) (σ x)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e439 X0 X1 X2
                 have i₂ := b21e162 (σ y) X0
                 grind)
              | exact superpose b21e162 b21e439
              | exact resolve b21e439 b21e162
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e162 b21e439
            have b21e576 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (σ (M.op x x)) X0) := by
              intro X0
              first
              | (have i₁ := b21e562 X0 x x
                 have i₂ := b21e119 x (M.op x (M.op x (σ y))) X0
                 grind)
              | exact superpose b21e119 b21e562
              | exact resolve b21e562 b21e119
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e119 b21e562
            have b21e579 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
              intro X0
              first
              | (have i₁ := b21e576 X0
                 have i₂ := b21e401 (σ y) X0
                 grind)
              | exact superpose b21e401 b21e576
              | exact resolve b21e576 b21e401
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e576
            have b21e633 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x x))) (σ y)) = (M.op (σ y) (M.op (M.op X1 (σ x)) (σ (M.op x x)))) := by
              intro X0 X1
              first
              | (have i₁ := b21e35 X0 (σ x) (σ (M.op x x)) x
                 have i₂ := b21e168
                 grind)
              | exact superpose b21e168 b21e35
              | exact resolve b21e35 b21e168
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e35 b21e168
            have b21e725 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x x))) (σ y)) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
              intro X0
              first
              | (have i₁ := b21e633 X0 x
                 have i₂ := b21e118 x (σ (M.op x x))
                 grind)
              | exact superpose b21e118 b21e633
              | exact resolve b21e633 b21e118
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e118 b21e633
            have b21e740 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
              first
              | (have i₁ := b21e725 x
                 have i₂ := b21e294 x (σ y)
                 grind)
              | exact superpose b21e294 b21e725
              | exact resolve b21e725 b21e294
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e294 b21e725
            have b21e745 : (σ (M.op y y)) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
              first
              | (have i₁ := b21e740
                 have i₂ := b21e32 y
                 grind)
              | exact superpose b21e32 b21e740
              | exact resolve b21e740 b21e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e740
            have b21e956 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b21e25
                 have i₂ := b21e62 y x
                 grind)
              | exact superpose b21e62 b21e25
              | (have j1 := b21e62 y x
                 grind)
              | exact resolve b21e25 b21e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e62
            have b21e1009 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have r₁ := b21e956
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e956 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e956
            have b21e1181 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b21e34 x
                 have i₂ := b21e401 x (σ x)
                 grind)
              | exact superpose b21e401 b21e34
              | exact resolve b21e34 b21e401
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e34 b21e401
            have b21e1217 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b21e1181
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e1181
              | exact resolve b21e1181 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1181
            have b21e1366 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b21e21
                 have i₂ := b21e1217
                 grind)
              | exact superpose b21e1217 b21e21
              | exact resolve b21e21 b21e1217
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e1385 : (σ y) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b21e1366
                 have i₂ := b21e66
                 grind)
              | exact superpose b21e66 b21e1366
              | exact resolve b21e1366 b21e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e66 b21e1366
            have b21e3929 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
              first
              | (have i₁ := b21e579 (M.op (σ y) (σ (M.op x x)))
                 have i₂ := b21e559 (σ (M.op x x))
                 grind)
              | exact superpose b21e559 b21e579
              | exact resolve b21e579 b21e559
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e559 b21e579
            have b21e3936 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op y y)) := by
              first
              | (have i₁ := b21e3929
                 have i₂ := b21e745
                 grind)
              | exact superpose b21e745 b21e3929
              | exact resolve b21e3929 b21e745
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e745 b21e3929
            have b21e4022 : (σ (M.op (M.op x x) (M.op x x))) = (σ (M.op y y)) := by
              first
              | (have i₁ := b21e3936
                 have i₂ := b21e32 (M.op x x)
                 grind)
              | exact superpose b21e32 b21e3936
              | exact resolve b21e3936 b21e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e32 b21e3936
            have b21e17690 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
              first
              | (have i₁ := b21e1217
                 have i₂ := b21e1009
                 grind)
              | exact superpose b21e1009 b21e1217
              | exact resolve b21e1217 b21e1009
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e1009 b21e1217
            have b21e17769 : (σ y) = (σ (k y x)) := by
              first
              | (have r₁ := b21e17690
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e17690 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e17690
            have b21e17786 : (k y x) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (k y x)
                 have i₂ := b21e17769
                 grind)
              | exact superpose b21e17769 b21e15
              | exact resolve b21e15 b21e17769
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e17769
            have b21e17825 : y = (k y x) := by
              first
              | (have i₁ := b21e17786
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e17786
              | exact resolve b21e17786 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e17786
            have b21e18458 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
              first
              | (have i₁ := b21e19 y x
                 have i₂ := b21e17825
                 grind)
              | exact superpose b21e17825 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e17825
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e18459 : x = (M.op x y) ∨ x = y := by
              first
              | (have r₁ := b21e18458
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e18458 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e18458
            have b21e18461 : x = (M.op x y) := by
              first
              | (have r₁ := b21e18459
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e18459 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e18459
            have b21e19425 : x = (M.op x x) := by
              first
              | (have i₁ := b21e71
                 have i₂ := b21e18461
                 grind)
              | exact superpose b21e18461 b21e71
              | exact resolve b21e71 b21e18461
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e71
            have b21e19431 : x ≠ x ∨ x = y ∨ (k y x) = (M.op y y) := by
              first
              | (have i₁ := b21e18 y x
                 have i₂ := b21e18461
                 grind)
              | exact superpose b21e18461 b21e18
              | (have j0 := b21e18 x y
                 grind)
              | (have r₁ := b21e18 y x
                 have r₂ := b21e18461
                 grind)
              | exact resolve b21e18 b21e18461
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e18461
            have b21e19462 : x = y ∨ (k y x) = (M.op y y) := by grind
            clear b21e19431
            have b21e19469 : (k y x) = (M.op y y) := by
              first
              | (have r₁ := b21e19462
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e19462 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e19462
            have b21e19474 : y = (M.op y y) := by
              first
              | (have i₁ := b21e19469
                 have i₂ := b21e17825
                 grind)
              | exact superpose b21e17825 b21e19469
              | exact resolve b21e19469 b21e17825
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e17825 b21e19469
            have b21e20103 : (σ (M.op x x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b21e4022
                 have i₂ := b21e19425
                 grind)
              | exact superpose b21e19425 b21e4022
              | exact resolve b21e4022 b21e19425
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e4022 b21e19425
            have b21e20165 : (σ y) = (σ (M.op x x)) := by
              first
              | (have i₁ := b21e20103
                 have i₂ := b21e19474
                 grind)
              | exact superpose b21e19474 b21e20103
              | exact resolve b21e20103 b21e19474
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e19474 b21e20103
            have b21e20176 : False := by grind
            exact b21e20176
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b22e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : False := by grind
              exact b22e30
            · have b23e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e30 : False := by grind
              exact b23e30
        · rcases eq_or_ne (x) (x) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : x ≠ y := by grind
            have b24e23 : y ≠ (M.op y x) := by grind
            have b24e24 : (σ x) ≠ (σ y) := by grind
            have b24e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
            have b24e684 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b24e25
                 have i₂ := b24e61 x y
                 grind)
              | exact superpose b24e61 b24e25
              | (have j1 := b24e61 x y
                 grind)
              | (have r₁ := b24e25
                 have r₂ := b24e61 x y
                 grind)
              | exact resolve b24e25 b24e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e61
            have b24e706 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
            clear b24e684
            have b24e714 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b24e706
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e706 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e706
            have b24e735 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e714
                 grind)
              | exact superpose b24e714 b24e21
              | exact resolve b24e21 b24e714
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e714
            have b24e796 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
              first
              | (have i₁ := b24e735
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e735
              | (have j1 := b24e19 x y
                 grind)
              | (have r₁ := b24e735
                 have r₂ := b24e19 (σ (M.op x y)) (σ (k x y))
                 grind)
              | (have r₁ := b24e735
                 have r₂ := b24e19 (σ (k x y)) (σ (M.op x y))
                 grind)
              | exact resolve b24e735 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e735
            have b24e797 : y = (M.op y x) ∨ x = y := by grind
            clear b24e796
            have b24e798 : x = y := by
              first
              | (have r₁ := b24e797
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e797 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e797
            have b24e799 : False := by grind
            exact b24e799
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b25e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : False := by grind
              exact b25e30
            · have b26e27 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : False := by grind
              exact b26e30

/-- `Equation4474`: `x ◇ (y ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pyx_pxy_Equation4474 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4474 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4474.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
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
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b0e15 X0 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have j0 := b0e15 X0 x
             grind)
          | (have r₁ := b0e15 X0 x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e27 : ∀ X0 : G, (k X0 x) = X0 := by
          intro X0
          first
          | (have j0 := b0e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24
        have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 X0 X1 X3
             have i₂ := b0e12 X0 X1 X2
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e12 x x x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e41 X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e41
          | exact resolve b0e41 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 X0 X1
             have i₂ := b0e17 (σ X0) (σ X1)
             grind)
          | exact superpose b0e17 b0e18
          | (have j1 := b0e17 (σ X1) (σ X1)
             grind)
          | exact resolve b0e18 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e2108 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e84 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e84
        have b0e2110 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e2108 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2108
        have b0e10120 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e2110 x
             have i₂ := b0e27 x
             grind)
          | exact superpose b0e27 b0e2110
          | (have j0 := b0e2110 x
             grind)
          | exact resolve b0e2110 b0e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e27 b0e2110
        have b0e10130 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e10120
        have b0e10219 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e36 (σ x) (σ x) x x
             have i₂ := b0e10130
             grind)
          | exact superpose b0e10130 b0e36
          | exact resolve b0e36 b0e10130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e18166 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e10130
             have i₂ := b0e10219 X0 (σ x)
             grind)
          | (have i₁ := b0e10130
             have i₂ := b0e10219 (σ x) X0
             grind)
          | exact superpose b0e10219 b0e10130
          | exact resolve b0e10130 b0e10219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e10130
        have b0e18167 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e19
             have i₂ := b0e10219 X0 (σ y)
             grind)
          | (have i₁ := b0e19
             have i₂ := b0e10219 (σ y) X0
             grind)
          | exact superpose b0e10219 b0e19
          | exact resolve b0e19 b0e10219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e10219
        have b0e18337 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e18167 X0
             have i₂ := b0e48 y
             grind)
          | exact superpose b0e48 b0e18167
          | exact resolve b0e18167 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48 b0e18167
        have b0e18406 : False := by grind
        exact b0e18406
      · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
        · have b1e23 : x ≠ (M.op x x) := by grind
          have b1e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : False := by grind
          exact b1e25
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op y y) := by grind
          have b2e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b2e24 : x ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X0 X1 X3
               have i₂ := b2e13 X0 X1 X2
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e48 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e13 (σ y) (σ y) x
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e49 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e13 y y x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e54 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e49 X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e49
            | exact resolve b2e49 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e49
          have b2e55 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e48 X0
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e48
            | exact resolve b2e48 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e48
          have b2e68 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b2e17 y X0
               have i₂ := b2e54 X0
               grind)
            | exact superpose b2e54 b2e17
            | (have j0 := b2e17 y X0
               grind)
            | (have r₁ := b2e17 y X0
               have r₂ := b2e54 X0
               grind)
            | exact resolve b2e17 b2e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e54
          have b2e69 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b2e68 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e68
          have b2e75 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b2e17 (σ y) X0
               have i₂ := b2e55 X0
               grind)
            | exact superpose b2e55 b2e17
            | (have j0 := b2e17 (σ y) X0
               grind)
            | (have r₁ := b2e17 (σ y) X0
               have r₂ := b2e55 X0
               grind)
            | exact resolve b2e17 b2e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e55
          have b2e77 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b2e75 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e75
          have b2e94 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X1 X1 X2
               have i₂ := b2e18 X0 X1
               grind)
            | exact superpose b2e18 b2e13
            | (have j1 := b2e18 X2 X0
               grind)
            | exact resolve b2e13 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e117 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k X0 (τ X1))
               have i₂ := b2e30 X1 X0
               grind)
            | exact superpose b2e30 b2e14
            | exact resolve b2e14 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30
          have b2e1495 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e17 X0 X1
               have i₂ := b2e94 X0 X1 X2
               grind)
            | (have i₁ := b2e17 X0 X0
               have i₂ := b2e94 X0 X1 X2
               grind)
            | exact superpose b2e94 b2e17
            | (have j0 := b2e17 X0 X1
               have j1 := b2e94 X0 X1 X2
               grind)
            | (have r₁ := b2e17 X2 X0
               have r₂ := b2e94 X0 X1 X2
               grind)
            | exact resolve b2e17 b2e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e94
          have b2e1630 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e1495 X0 X1 X2
               have j1 := b2e18 X2 X0
               grind)
            | (have r₁ := b2e1495 X1 X1 X2
               have r₂ := b2e18 X0 X1
               grind)
            | (have r₁ := b2e1495 X1 X1 X2
               have r₂ := b2e18 X1 X1
               grind)
            | exact resolve b2e1495 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1495
          have b2e2423 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e44 X0 X0 X2 x
               have i₂ := b2e69 X0
               grind)
            | exact superpose b2e69 b2e44
            | (have j1 := b2e69 X0
               grind)
            | exact resolve b2e44 b2e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e4639 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e44 X0 X0 X2 x
               have i₂ := b2e77 X0
               grind)
            | exact superpose b2e77 b2e44
            | (have j1 := b2e77 X0
               grind)
            | exact resolve b2e44 b2e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44
          have b2e4690 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e19 y X0
               have i₂ := b2e77 (σ X0)
               grind)
            | exact superpose b2e77 b2e19
            | (have j1 := b2e77 (σ X0)
               grind)
            | exact resolve b2e19 b2e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e77
          have b2e75999 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e1630 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1630
          have b2e76000 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e75999 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e75999
          have b2e76001 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e76000 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e76000
          have b2e202152 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x y) = (k y x) := by
            intro X0
            first
            | (have i₁ := b2e24
               have i₂ := b2e2423 x x X0
               grind)
            | (have i₁ := b2e24
               have i₂ := b2e2423 x X0 x
               grind)
            | exact superpose b2e2423 b2e24
            | (have j1 := b2e2423 x x x
               grind)
            | exact resolve b2e24 b2e2423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e202167 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e69 X0
               have i₂ := b2e2423 X0 X0 X1
               grind)
            | (have i₁ := b2e69 X0
               have i₂ := b2e2423 X0 X1 X0
               grind)
            | exact superpose b2e2423 b2e69
            | (have j0 := b2e69 X0
               have j1 := b2e2423 X0 X1 x
               grind)
            | exact resolve b2e69 b2e2423
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e69 b2e2423
          have b2e202956 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 y) = (k y X0) := by
            intro X0 X1
            first
            | (have j0 := b2e202167 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e202167
          have b2e203001 : (M.op x y) = (k y x) := by
            first
            | (have j1 := b2e202956 x x
               grind)
            | (have r₁ := b2e202152 x
               have r₂ := b2e202956 x x
               grind)
            | exact resolve b2e202152 b2e202956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e202152 b2e202956
          have b2e219332 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b2e20
               have i₂ := b2e4639 (σ x) (σ y) X0
               grind)
            | (have i₁ := b2e20
               have i₂ := b2e4639 (σ x) X0 (σ y)
               grind)
            | exact superpose b2e4639 b2e20
            | (have j1 := b2e4639 (σ x) x x
               grind)
            | exact resolve b2e20 b2e4639
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e4639
          have b2e219483 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e219332 X0
               have i₂ := b2e19 y x
               grind)
            | exact superpose b2e19 b2e219332
            | (have j0 := b2e219332 X0
               grind)
            | exact resolve b2e219332 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e219332
          have b2e219546 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b2e219483 X0
               have i₂ := b2e203001
               grind)
            | exact superpose b2e203001 b2e219483
            | (have j0 := b2e219483 X0
               grind)
            | exact resolve b2e219483 b2e203001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e219483
          have b2e219567 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b2e219546 X0
               grind)
            | (have r₁ := b2e219546 X0
               have r₂ := b2e20
               grind)
            | exact resolve b2e219546 b2e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e219546
          have b2e237927 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e219567 (σ y)
               have i₂ := b2e4690 x
               grind)
            | exact superpose b2e4690 b2e219567
            | (have j1 := b2e4690 x
               grind)
            | exact resolve b2e219567 b2e4690
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e4690 b2e219567
          have b2e238177 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e237927
               have i₂ := b2e203001
               grind)
            | exact superpose b2e203001 b2e237927
            | exact resolve b2e237927 b2e203001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e203001 b2e237927
          have b2e238178 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b2e238177
          have b2e238217 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b2e16 X0 (σ x)
               have i₂ := b2e238178
               grind)
            | exact superpose b2e238178 b2e16
            | (have j0 := b2e16 X0 (σ x)
               grind)
            | (have r₁ := b2e16 X0 (σ x)
               have r₂ := b2e238178
               grind)
            | exact resolve b2e16 b2e238178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e238178
          have b2e238378 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b2e238217 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e238217
          have b2e238590 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
            intro X0
            first
            | (have i₁ := b2e117 X0 (σ x)
               have i₂ := b2e238378 (σ X0)
               grind)
            | exact superpose b2e238378 b2e117
            | exact resolve b2e117 b2e238378
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e117 b2e238378
          have b2e238645 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b2e238590 X0
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e238590
            | exact resolve b2e238590 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e238590
          have b2e238656 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b2e238645 X0
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e238645
            | exact resolve b2e238645 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e238645
          have b2e239991 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b2e76001 x
               have i₂ := b2e238656 x
               grind)
            | exact superpose b2e238656 b2e76001
            | (have j0 := b2e76001 x
               grind)
            | exact resolve b2e76001 b2e238656
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e76001 b2e238656
          have b2e240078 : x = (M.op x x) := by grind
          clear b2e239991
          have b2e240138 : False := by grind
          exact b2e240138
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e39 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e13 x x x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e46 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b3e39 X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e39
            | exact resolve b3e39 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e39
          have b3e68 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e25
               have i₂ := b3e46 y
               grind)
            | exact superpose b3e46 b3e25
            | exact resolve b3e25 b3e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25 b3e46
          have b3e75 : False := by grind
          exact b3e75
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b4e25 : x ≠ (M.op x x) := by grind
            have b4e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : False := by grind
            exact b4e27
          · have b5e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op y y) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b5e17 X0 y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e17
              | (have j0 := b5e17 X0 y
                 grind)
              | (have r₁ := b5e17 X0 y
                 have r₂ := b5e22
                 grind)
              | exact resolve b5e17 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e29 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b5e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e28
            have b5e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b5e20 (τ X0) X1
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e20
              | exact resolve b5e20 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e33 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b5e30 X0 y
                 have i₂ := b5e29 (τ X0)
                 grind)
              | exact superpose b5e29 b5e30
              | exact resolve b5e30 b5e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29 b5e30
            have b5e37 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e33 X0
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e33
              | exact resolve b5e33 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e33
            have b5e89 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e23
                 have i₂ := b5e19 X0 (σ y)
                 grind)
              | exact superpose b5e19 b5e23
              | (have j1 := b5e19 X0 (σ y)
                 grind)
              | (have r₁ := b5e23
                 have r₂ := b5e19 X0 (σ y)
                 grind)
              | (have r₁ := b5e23
                 have r₂ := b5e19 (σ y) (σ y)
                 grind)
              | exact resolve b5e23 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e90 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b5e89 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e89
            have b5e96 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e90 X0
                 have i₂ := b5e37 X0
                 grind)
              | exact superpose b5e37 b5e90
              | (have j0 := b5e90 X0
                 grind)
              | exact resolve b5e90 b5e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e37 b5e90
            have b5e97 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b5e96 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e96
            have b5e108 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e97 (σ y)
                 grind)
              | exact superpose b5e97 b5e23
              | (have r₁ := b5e23
                 have r₂ := b5e97 (σ y)
                 grind)
              | exact resolve b5e23 b5e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e97
            have b5e109 : False := by grind
            exact b5e109
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y y) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e25 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 X0 y
               grind)
            | (have r₁ := b6e16 X0 y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e28 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b6e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e25
          have b6e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 (τ X0) X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e94 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e29 X0 y
               have i₂ := b6e28 (τ X0)
               grind)
            | exact superpose b6e28 b6e29
            | exact resolve b6e29 b6e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28 b6e29
          have b6e99 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e94 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e94
            | exact resolve b6e94 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e94
          have b6e113 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e18 X0 (σ y)
               have i₂ := b6e99 X0
               grind)
            | exact superpose b6e99 b6e18
            | (have j0 := b6e18 X0 (σ y)
               grind)
            | exact resolve b6e18 b6e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e99
          have b6e115 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have j0 := b6e113 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e113
          have b6e118 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b6e115 X0
               grind)
            | (have r₁ := b6e115 (σ y)
               have r₂ := b6e22
               grind)
            | (have r₁ := b6e115 X0
               have r₂ := b6e22
               grind)
            | exact resolve b6e115 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e115
          have b6e276 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e118 (σ x)
               grind)
            | exact superpose b6e118 b6e23
            | (have r₁ := b6e23
               have r₂ := b6e118 (σ x)
               grind)
            | exact resolve b6e23 b6e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e118
          have b6e277 : False := by grind
          exact b6e277
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b7e25 : x ≠ (M.op x x) := by grind
            have b7e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : False := by grind
            exact b7e27
          · have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op y y) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b8e17 X0 y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 X0 y
                 grind)
              | (have r₁ := b8e17 X0 y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e28 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b8e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e27
            have b8e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b8e20 (τ X0) X1
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e20
              | exact resolve b8e20 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e29 X0 y
                 have i₂ := b8e28 (τ X0)
                 grind)
              | exact superpose b8e28 b8e29
              | exact resolve b8e29 b8e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28 b8e29
            have b8e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e32 X0
                 have i₂ := b8e16 X0
                 grind)
              | exact superpose b8e16 b8e32
              | exact resolve b8e32 b8e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e32
            have b8e82 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e23
                 have i₂ := b8e19 X0 (σ y)
                 grind)
              | exact superpose b8e19 b8e23
              | (have j1 := b8e19 X0 (σ y)
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e19 X0 (σ y)
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e19 (σ y) (σ y)
                 grind)
              | exact resolve b8e23 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e83 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b8e82 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e82
            have b8e89 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b8e83 X0
                 have i₂ := b8e36 X0
                 grind)
              | exact superpose b8e36 b8e83
              | (have j0 := b8e83 X0
                 grind)
              | exact resolve b8e83 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36 b8e83
            have b8e90 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b8e89 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e89
            have b8e103 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b8e24
                 have i₂ := b8e90 (σ x)
                 grind)
              | exact superpose b8e90 b8e24
              | (have r₁ := b8e24
                 have r₂ := b8e90 (σ x)
                 grind)
              | exact resolve b8e24 b8e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e90
            have b8e104 : False := by grind
            exact b8e104
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b9e16 X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 X0 (σ y)
               grind)
            | (have r₁ := b9e16 X0 (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b9e27 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e27
          have b9e33 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 y
               have i₂ := b9e28 (σ X0)
               grind)
            | exact superpose b9e28 b9e19
            | exact resolve b9e19 b9e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e28
          have b9e101 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b9e14 (k X0 y)
               have i₂ := b9e33 X0
               grind)
            | exact superpose b9e33 b9e14
            | exact resolve b9e14 b9e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e33
          have b9e102 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b9e101 X0
               have i₂ := b9e14 X0
               grind)
            | exact superpose b9e14 b9e101
            | exact resolve b9e101 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e101
          have b9e125 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b9e18 X0 y
               have i₂ := b9e102 X0
               grind)
            | exact superpose b9e102 b9e18
            | (have j0 := b9e18 X0 y
               grind)
            | exact resolve b9e18 b9e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e102
          have b9e126 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
            intro X0
            first
            | (have j0 := b9e125 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e125
          have b9e128 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b9e126 X0
               grind)
            | (have r₁ := b9e126 y
               have r₂ := b9e21
               grind)
            | (have r₁ := b9e126 X0
               have r₂ := b9e21
               grind)
            | exact resolve b9e126 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e126
          have b9e147 : y ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e128 y
               grind)
            | exact superpose b9e128 b9e21
            | (have r₁ := b9e21
               have r₂ := b9e128 y
               grind)
            | exact resolve b9e21 b9e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e128
          have b9e154 : False := by grind
          exact b9e154
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b10e25 : x ≠ (M.op x x) := by grind
            have b10e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : False := by grind
            exact b10e27
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op y y) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b11e17 X0 (σ y)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e17
              | (have j0 := b11e17 X0 (σ y)
                 grind)
              | (have r₁ := b11e17 X0 (σ y)
                 have r₂ := b11e24
                 grind)
              | exact resolve b11e17 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e29 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b11e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e28
            have b11e33 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b11e29 (σ X0)
                 have i₂ := b11e20 X0 y
                 grind)
              | exact superpose b11e20 b11e29
              | exact resolve b11e29 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e36 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b11e15 (k X0 y)
                 have i₂ := b11e33 X0
                 grind)
              | exact superpose b11e33 b11e15
              | exact resolve b11e15 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33
            have b11e37 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b11e36 X0
                 have i₂ := b11e15 X0
                 grind)
              | exact superpose b11e15 b11e36
              | exact resolve b11e36 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e36
            have b11e74 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b11e37 X0
                 have i₂ := b11e19 X0 y
                 grind)
              | exact superpose b11e19 b11e37
              | (have j1 := b11e19 X0 y
                 grind)
              | exact resolve b11e37 b11e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e37
            have b11e82 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
              intro X0
              first
              | (have j0 := b11e74 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e74
            have b11e88 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b11e82 X0
                 grind)
              | (have r₁ := b11e82 y
                 have r₂ := b11e22
                 grind)
              | (have r₁ := b11e82 X0
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e82 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e82
            have b11e92 : y ≠ y := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e88 y
                 grind)
              | exact superpose b11e88 b11e22
              | (have r₁ := b11e22
                 have r₂ := b11e88 y
                 grind)
              | exact resolve b11e22 b11e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e88
            have b11e99 : False := by grind
            exact b11e99
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : x = (M.op x y) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e27 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e28 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e27
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e27
              | exact resolve b12e27 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e27
            have b12e29 : False := by grind
            exact b12e29
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b13e27 : x ≠ (M.op x x) := by grind
              have b13e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : False := by grind
              exact b13e29
            · have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : x = (M.op x y) := by grind
              have b14e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e22
                | exact resolve b14e22 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e30 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b14e29
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e29
                | exact resolve b14e29 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e29
              have b14e31 : False := by grind
              exact b14e31
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e28 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e17 X0 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e17
              | (have j0 := b15e17 X0 x
                 grind)
              | (have r₁ := b15e17 X0 x
                 have r₂ := b15e26
                 grind)
              | exact resolve b15e17 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e29 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e28 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28
            have b15e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e14 X0 X1 X3
                 have i₂ := b15e14 X0 X1 X2
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X0 X1
                 have i₂ := b15e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X1) (σ X1)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e1760 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e79 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e79
            have b15e1762 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b15e1760 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1760
            have b15e7930 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e1762 x
                 have i₂ := b15e29 x
                 grind)
              | exact superpose b15e29 b15e1762
              | (have j0 := b15e1762 x
                 grind)
              | exact resolve b15e1762 b15e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e29 b15e1762
            have b15e7936 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b15e7930
            have b15e8024 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e40 (σ x) (σ x) x x
                 have i₂ := b15e7936
                 grind)
              | exact superpose b15e7936 b15e40
              | exact resolve b15e40 b15e7936
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e40
            have b15e12268 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e7936
                 have i₂ := b15e8024 X0 (σ x)
                 grind)
              | (have i₁ := b15e7936
                 have i₂ := b15e8024 (σ x) X0
                 grind)
              | exact superpose b15e8024 b15e7936
              | exact resolve b15e7936 b15e8024
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e7936
            have b15e12269 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e8024 X0 (σ y)
                 grind)
              | (have i₁ := b15e25
                 have i₂ := b15e8024 (σ y) X0
                 grind)
              | exact superpose b15e8024 b15e25
              | exact resolve b15e25 b15e8024
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e8024
            have b15e12287 : False := by grind
            exact b15e12287
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b16e27 : x ≠ (M.op x x) := by grind
              have b16e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : False := by grind
              exact b16e29
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b17e24 : x = (M.op x y) := by grind
              have b17e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e36 : ∀ X0 : G, (M.op x (M.op y y)) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e15 x y X0
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e45 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e36 X1
                   have i₂ := b17e36 X0
                   grind)
                | (have i₁ := b17e36 X0
                   have i₂ := b17e36 (M.op y y)
                   grind)
                | exact superpose b17e36 b17e36
                | exact resolve b17e36 b17e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36
              have b17e104 : ∀ X0 : G, x ≠ (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e28
                   have i₂ := b17e45 x X0
                   grind)
                | (have i₁ := b17e28
                   have i₂ := b17e45 X0 x
                   grind)
                | exact superpose b17e45 b17e28
                | exact resolve b17e28 b17e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e105 : ∀ X0 : G, x = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e24
                   have i₂ := b17e45 y X0
                   grind)
                | (have i₁ := b17e24
                   have i₂ := b17e45 X0 y
                   grind)
                | exact superpose b17e45 b17e24
                | exact resolve b17e24 b17e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e45
              have b17e106 : False := by grind
              exact b17e106
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            grind
          have b18e22 : x ≠ (M.op x y) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e41 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b18e13 x x x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e46 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b18e41 X0
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e41
            | exact resolve b18e41 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e41
          have b18e54 : x ≠ x := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e46 y
               grind)
            | exact superpose b18e46 b18e22
            | (have r₁ := b18e22
               have r₂ := b18e46 y
               grind)
            | exact resolve b18e22 b18e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e46
          have b18e55 : False := by grind
          exact b18e55
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b19e25 : x ≠ (M.op x x) := by grind
            have b19e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : False := by grind
            exact b19e27
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y y) := by grind
            have b20e23 : x ≠ (M.op x y) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 X0 (σ y)
                 grind)
              | (have r₁ := b20e17 X0 (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b20e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e27
            have b20e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 y
                 have i₂ := b20e28 (σ X0)
                 grind)
              | exact superpose b20e28 b20e20
              | exact resolve b20e20 b20e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e15 (k X0 y)
                 have i₂ := b20e32 X0
                 grind)
              | exact superpose b20e32 b20e15
              | exact resolve b20e15 b20e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e36 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e35 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e35
              | exact resolve b20e35 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e75 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e36 X0
                 have i₂ := b20e19 X0 y
                 grind)
              | exact superpose b20e19 b20e36
              | (have j1 := b20e19 X0 y
                 grind)
              | exact resolve b20e36 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e83 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
              intro X0
              first
              | (have j0 := b20e75 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e75
            have b20e89 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b20e83 X0
                 grind)
              | (have r₁ := b20e83 y
                 have r₂ := b20e22
                 grind)
              | (have r₁ := b20e83 X0
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e83 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e83
            have b20e94 : x ≠ x := by
              first
              | (have i₁ := b20e23
                 have i₂ := b20e89 x
                 grind)
              | exact superpose b20e89 b20e23
              | (have r₁ := b20e23
                 have r₂ := b20e89 x
                 grind)
              | exact resolve b20e23 b20e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e89
            have b20e101 : False := by grind
            exact b20e101
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b21e23 : x ≠ (M.op x y) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e39 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e14 x x x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e44 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b21e39 X0
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e39
              | exact resolve b21e39 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e39
            have b21e52 : x ≠ x := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e44 y
                 grind)
              | exact superpose b21e44 b21e23
              | (have r₁ := b21e23
                 have r₂ := b21e44 y
                 grind)
              | exact resolve b21e23 b21e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e44
            have b21e53 : False := by grind
            exact b21e53
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b22e27 : x ≠ (M.op x x) := by grind
              have b22e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : False := by grind
              exact b22e29
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              have b23e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X0 X1 X3
                   have i₂ := b23e15 X0 X1 X2
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e98 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e38 (σ x) (σ y) x x
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e38
                | exact resolve b23e38 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38
              have b23e144 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e18 X1 (σ x)
                   have i₂ := b23e98 (σ x) X0
                   grind)
                | (have i₁ := b23e18 X1 (σ x)
                   have i₂ := b23e98 X0 (σ x)
                   grind)
                | exact superpose b23e98 b23e18
                | (have j0 := b23e18 X1 (σ x)
                   grind)
                | exact resolve b23e18 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e149 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b23e26
                   have i₂ := b23e98 (σ y) X0
                   grind)
                | (have i₁ := b23e26
                   have i₂ := b23e98 X0 (σ y)
                   grind)
                | exact superpose b23e98 b23e26
                | exact resolve b23e26 b23e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e98
              have b23e153 : ∀ X1 : G, (k X1 (σ x)) = X1 := by
                intro X1
                first
                | (have j0 := b23e144 x X1
                   grind)
                | (have r₁ := b23e144 x X1
                   have r₂ := b23e149 x
                   grind)
                | exact resolve b23e144 b23e149
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e144 b23e149
              have b23e194 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 x
                   have i₂ := b23e153 (σ X0)
                   grind)
                | exact superpose b23e153 b23e21
                | exact resolve b23e21 b23e153
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e153
              have b23e523 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b23e16 (k X0 x)
                   have i₂ := b23e194 X0
                   grind)
                | exact superpose b23e194 b23e16
                | exact resolve b23e16 b23e194
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e194
              have b23e524 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e523 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e523
                | exact resolve b23e523 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e523
              have b23e745 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x x) ∨ (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e20 X0 x
                   have i₂ := b23e524 X0
                   grind)
                | exact superpose b23e524 b23e20
                | (have j0 := b23e20 X0 x
                   grind)
                | exact resolve b23e20 b23e524
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e524
              have b23e746 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x x) := by
                intro X0
                first
                | (have j0 := b23e745 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e745
              have b23e748 : ∀ X0 : G, (M.op X0 x) = X0 := by
                intro X0
                first
                | (have j0 := b23e746 X0
                   grind)
                | (have r₁ := b23e746 x
                   have r₂ := b23e28
                   grind)
                | (have r₁ := b23e746 X0
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e746 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e746
              have b23e1020 : x ≠ x := by
                first
                | (have i₁ := b23e28
                   have i₂ := b23e748 x
                   grind)
                | exact superpose b23e748 b23e28
                | (have r₁ := b23e28
                   have r₂ := b23e748 x
                   grind)
                | exact resolve b23e28 b23e748
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e748
              have b23e1043 : False := by grind
              exact b23e1043
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              grind
            have b24e23 : x ≠ (M.op x y) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e35 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b24e14 x x x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e43 : ∀ X0 : G, x = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b24e35 X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e35
              | exact resolve b24e35 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e35
            have b24e49 : x ≠ x := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e43 y
                 grind)
              | exact superpose b24e43 b24e23
              | (have r₁ := b24e23
                 have r₂ := b24e43 y
                 grind)
              | exact resolve b24e23 b24e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e43
            have b24e50 : False := by grind
            exact b24e50
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b25e27 : x ≠ (M.op x x) := by grind
              have b25e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : False := by grind
              exact b25e29
            · have b26e20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op y y) := by grind
              have b26e24 : x ≠ (M.op x y) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e78 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (σ y)
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ y) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e79 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have j0 := b26e78 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e78
              have b26e824 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 y
                   have i₂ := b26e79 (σ X0)
                   grind)
                | exact superpose b26e79 b26e21
                | (have j1 := b26e79 (σ X0)
                   grind)
                | exact resolve b26e21 b26e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79
              have b26e30111 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e824 x
                   grind)
                | exact superpose b26e824 b26e22
                | (have j1 := b26e824 x
                   grind)
                | exact resolve b26e22 b26e824
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e824
              have b26e30241 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b26e30111
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e30111 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30111
              have b26e30247 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e30241
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e30241
                | (have j1 := b26e20 y y
                   grind)
                | exact resolve b26e30241 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30241
              have b26e30248 : y = (M.op y y) ∨ x = (M.op x y) := by grind
              clear b26e30247
              have b26e30251 : x = (M.op x y) := by
                first
                | (have r₁ := b26e30248
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e30248 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30248
              have b26e30254 : False := by grind
              exact b26e30254

/-- `Equation4485`: `x ◇ (y ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyy_x_pxy_Equation4485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e33 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (σ x) X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 X0 X3
             have i₂ := b1e12 X2 X0 X1
             grind)
          | (have i₁ := b1e12 (M.op X1 X2) X1 X2
             have i₂ := b1e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op x X0) := by
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
        have b1e48 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
        have b1e51 : (M.op y y) = (k x y) := by grind
        clear b1e50
        have b1e52 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e48
          | exact resolve b1e48 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e55 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        have b1e58 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e55
             have r₂ := b1e21
             grind)
          | exact resolve b1e55 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e59 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e60 : (σ x) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e59
          | exact resolve b1e59 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e59
        have b1e63 : (M.op y y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e13
          | exact resolve b1e13 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e64 : x = (M.op y y) := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e63
          | exact resolve b1e63 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e87 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e64
             grind)
          | exact superpose b1e64 b1e12
          | exact resolve b1e12 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e93 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 x X1
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e12
          | exact resolve b1e12 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e133 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e33 X0 x
             have i₂ := b1e87 (σ x)
             grind)
          | exact superpose b1e87 b1e33
          | exact resolve b1e33 b1e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e161 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b1e133 X0
             have i₂ := b1e12 X0 x (σ x)
             grind)
          | exact superpose b1e12 b1e133
          | exact resolve b1e133 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e133
        have b1e171 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e161 X0
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e161
          | exact resolve b1e161 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e161
        have b1e226 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e34 X0 X1 X2 x
             have i₂ := b1e87 X0
             grind)
          | (have i₁ := b1e34 x X1 X2 X0
             have i₂ := b1e87 X0
             grind)
          | exact superpose b1e87 b1e34
          | exact resolve b1e34 b1e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e281 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e226 X0 X1 X2
             have i₂ := b1e93 X2 X0
             grind)
          | exact superpose b1e93 b1e226
          | exact resolve b1e226 b1e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93 b1e226
        have b1e318 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op (M.op X0 X2) (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e34 X0 X1 (σ y) X2
             have i₂ := b1e171 (M.op X0 X1)
             grind)
          | exact superpose b1e171 b1e34
          | exact resolve b1e34 b1e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e325 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e318 X0 X1 x
             have i₂ := b1e281 X0 x (σ y)
             grind)
          | exact superpose b1e281 b1e318
          | exact resolve b1e318 b1e281
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e281 b1e318
        have b1e338 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e325 X0 X1
             have i₂ := b1e171 x
             grind)
          | exact superpose b1e171 b1e325
          | exact resolve b1e325 b1e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e171 b1e325
        have b1e6260 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e73 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e73
          | exact resolve b1e73 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e6380 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b1e6260
        have b1e6441 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b1e6380
             have r₂ := b1e52
             grind)
          | exact resolve b1e6380 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e6380
        have b1e6532 : (k x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e6441
             grind)
          | exact superpose b1e6441 b1e13
          | exact resolve b1e13 b1e6441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6548 : y = (k x x) := by
          first
          | (have i₁ := b1e6532
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e6532
          | exact resolve b1e6532 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6532
        have b1e6636 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e6548
             grind)
          | exact superpose b1e6548 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e6548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e6637 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b1e6636
        have b1e9191 : y = (M.op x y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e338 x x
             have i₂ := b1e6637
             grind)
          | exact superpose b1e6637 b1e338
          | exact resolve b1e338 b1e6637
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e338
        have b1e9192 : x ≠ y ∨ x = (M.op x x) := by grind
        clear b1e6637
        have b1e9193 : x = y ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e9191
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e9191
          | exact resolve b1e9191 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9191
        have b1e9210 : x = (M.op x x) := by
          first
          | (have r₁ := b1e9193
             have r₂ := b1e9192
             grind)
          | exact resolve b1e9193 b1e9192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9192 b1e9193
        have b1e9820 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e9210
             grind)
          | exact superpose b1e9210 b1e15
          | (have r₁ := b1e15 x x
             have r₂ := b1e9210
             grind)
          | exact resolve b1e15 b1e9210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9210
        have b1e9837 : x = (k x x) := by grind
        clear b1e9820
        have b1e10721 : x = y := by
          first
          | (have i₁ := b1e6548
             have i₂ := b1e9837
             grind)
          | exact superpose b1e9837 b1e6548
          | exact resolve b1e6548 b1e9837
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6548
        have b1e10722 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e6441
             have i₂ := b1e9837
             grind)
          | exact superpose b1e9837 b1e6441
          | exact resolve b1e6441 b1e9837
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6441 b1e9837
        have b1e11723 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e10721
             grind)
          | exact superpose b1e10721 b1e21
          | exact resolve b1e21 b1e10721
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10721
        have b1e11740 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e11723
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e11723
          | exact resolve b1e11723 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e11723
        have b1e11742 : False := by grind
        exact b1e11742
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e28 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e18 X2 (k (τ X0) X1)
             have i₂ := b2e25 X0 X1
             grind)
          | exact superpose b2e25 b2e18
          | exact resolve b2e18 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e25 X0 X1
             grind)
          | exact superpose b2e25 b2e13
          | exact resolve b2e13 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X0 X3
             have i₂ := b2e12 X2 X0 X1
             grind)
          | (have i₁ := b2e12 (M.op X1 X2) X1 X2
             have i₂ := b2e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op x X0) := by
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
        have b2e36 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 X2 (M.op X0 X0)
             have i₂ := b2e12 X2 X0 X1
             grind)
          | (have i₁ := b2e12 X0 (M.op X1 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x X1
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e12
          | exact resolve b2e12 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op x x)
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e12
          | exact resolve b2e12 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : x ≠ x ∨ (M.op y y) = (k x y) := by
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
        have b2e48 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X2 (M.op X0 X0)
             have i₂ := b2e12 X2 X0 X1
             grind)
          | (have i₁ := b2e15 (M.op X1 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X2 (M.op X0 X0)
             grind)
          | (have r₁ := b2e15 (M.op X0 (M.op X0 X0)) X0
             have r₂ := b2e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op (M.op x x) (M.op x x)) = (k X0 (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 (M.op x x)
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e15
          | (have j0 := b2e15 X0 (M.op x x)
             grind)
          | exact resolve b2e15 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (M.op X0 X0) = (k (M.op X1 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op X1 X2) X0
             have i₂ := b2e12 X0 X1 X2
             grind)
          | (have i₁ := b2e15 X0 (M.op X1 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op X1 X2) X0
             grind)
          | (have r₁ := b2e15 (M.op X0 (M.op X0 X0)) X0
             have r₂ := b2e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op y y) = (k x y) := by grind
        clear b2e47
        have b2e52 : ∀ X0 : G, (M.op x (M.op x x)) = (k X0 (M.op x x)) ∨ (M.op x X0) ≠ X0 := by
          intro X0
          first
          | (have i₁ := b2e49 X0
             have i₂ := b2e41 (M.op x x) x
             grind)
          | exact superpose b2e41 b2e49
          | (have j0 := b2e49 X0
             grind)
          | exact resolve b2e49 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e53 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op x x) = (k X0 (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b2e52 X0
             have i₂ := b2e35 x
             grind)
          | exact superpose b2e35 b2e52
          | (have j0 := b2e52 X0
             grind)
          | (have r₁ := b2e52 (M.op x x)
             have r₂ := b2e35 x
             grind)
          | exact resolve b2e52 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X0))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X0))) := by
          intro X0 X1
          grind
        have b2e57 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
          intro X0
          grind
        have b2e58 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e57 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e57
          | (have j0 := b2e57 X0
             grind)
          | exact resolve b2e57 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e60 : ∀ X0 : G, (τ X0) = (M.op (M.op x (τ X0)) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e58 X0
             have i₂ := b2e43 (τ X0) (τ X0)
             grind)
          | exact superpose b2e43 b2e58
          | (have j0 := b2e58 X0
             grind)
          | exact resolve b2e58 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43 b2e58
        have b2e62 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op x x)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e60 X0
             have i₂ := b2e12 (τ X0) x (τ X0)
             grind)
          | exact superpose b2e12 b2e60
          | (have j0 := b2e60 X0
             grind)
          | exact resolve b2e60 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e64 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e62 X0
             have i₂ := b2e35 (τ X0)
             grind)
          | exact superpose b2e35 b2e62
          | (have j0 := b2e62 X0
             grind)
          | exact resolve b2e62 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e74 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e35 (M.op x X0)
             have i₂ := b2e41 (M.op x x) X0
             grind)
          | exact superpose b2e41 b2e35
          | exact resolve b2e35 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e78 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e74 X0
             have i₂ := b2e35 x
             grind)
          | exact superpose b2e35 b2e74
          | exact resolve b2e74 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e98 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e99 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 X3) X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X2 X3
             have i₂ := b2e17 X2 X0
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 X0 (M.op X1 X1)
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X2 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e100 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op (M.op X1 X2) (M.op X1 X1)) = X0 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op X1 X1) X1 X2
             have i₂ := b2e17 (M.op X1 X1) X0
             grind)
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e17 X0 (M.op X0 (M.op X1 X1))
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 (M.op X1 X1) X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e106 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
        have b2e107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e98 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e134 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e137 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e30 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e30
          | exact resolve b2e30 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e141 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e30 X0 X1
             have i₂ := b2e17 X0 (σ X1)
             grind)
          | exact superpose b2e17 b2e30
          | (have j1 := b2e17 X0 (σ X1)
             grind)
          | exact resolve b2e30 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e165 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e33 X0 X1 X2 (M.op x x)
             have i₂ := b2e35 X0
             grind)
          | exact superpose b2e35 b2e33
          | exact resolve b2e33 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e202 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e165 X0 X1 X2
             have i₂ := b2e41 X2 X0
             grind)
          | exact superpose b2e41 b2e165
          | exact resolve b2e165 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e165
        have b2e228 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 x
             have i₂ := b2e202 X1 x X0
             grind)
          | exact superpose b2e202 b2e12
          | exact resolve b2e12 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e233 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (M.op x x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e35 (M.op X0 X1)
             have i₂ := b2e202 X0 X1 (M.op x x)
             grind)
          | exact superpose b2e202 b2e35
          | exact resolve b2e35 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e236 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op x X0) ∨ (M.op X0 X0) = (k (M.op X1 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 (M.op X1 X2) X0
             have i₂ := b2e202 X1 X2 X0
             grind)
          | exact superpose b2e202 b2e15
          | (have j0 := b2e15 (M.op X1 X2) X0
             grind)
          | (have r₁ := b2e15 (M.op x X2) X2
             have r₂ := b2e202 x X2 X2
             grind)
          | exact resolve b2e15 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e241 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e233 X0 X1
             have i₂ := b2e78 x
             grind)
          | exact superpose b2e78 b2e233
          | exact resolve b2e233 b2e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78 b2e233
        have b2e314 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ X3 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = (k X3 (M.op X2 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e15 X3 (M.op X2 X2)
             have i₂ := b2e36 X0 X1 X2 X3
             grind)
          | (have i₁ := b2e15 (M.op (M.op X0 X1) X2) X3
             have i₂ := b2e36 X0 X1 X2 X3
             grind)
          | exact superpose b2e36 b2e15
          | (have j0 := b2e15 X3 (M.op X2 X2)
             grind)
          | exact resolve b2e15 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e354 : ∀ X2 X3 : G, (M.op x X3) ≠ X3 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = (k X3 (M.op X2 X2)) := by
          intro X2 X3
          first
          | (have i₁ := b2e314 x x X2 X3
             have i₂ := b2e202 (M.op x x) X2 X3
             grind)
          | exact superpose b2e202 b2e314
          | (have j0 := b2e314 x x X2 X3
             grind)
          | exact resolve b2e314 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e314
        have b2e400 : ∀ X2 X3 : G, (k X3 (M.op X2 X2)) = (M.op x (M.op X2 X2)) ∨ (M.op x X3) ≠ X3 := by
          intro X2 X3
          first
          | (have i₁ := b2e354 X2 X3
             have i₂ := b2e202 X2 X2 (M.op X2 X2)
             grind)
          | exact superpose b2e202 b2e354
          | (have j0 := b2e354 X2 X3
             grind)
          | exact resolve b2e354 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e354
        have b2e435 : ∀ X2 X3 : G, (M.op x X3) ≠ X3 ∨ (M.op x x) = (k X3 (M.op X2 X2)) := by
          intro X2 X3
          first
          | (have i₁ := b2e400 X2 X3
             have i₂ := b2e241 X2 X2
             grind)
          | exact superpose b2e241 b2e400
          | (have j0 := b2e400 X2 X3
             grind)
          | (have r₁ := b2e400 X2 (M.op x x)
             have r₂ := b2e241 x x
             grind)
          | exact resolve b2e400 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e400
        have b2e1446 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e134 (k (τ X0) X1) X2
             have i₂ := b2e25 X0 X1
             grind)
          | exact superpose b2e25 b2e134
          | exact resolve b2e134 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3094 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e30 X0 X1
             have i₂ := b2e107 (σ X1) X0
             grind)
          | exact superpose b2e107 b2e30
          | (have j1 := b2e107 (σ X1) X0
             grind)
          | exact resolve b2e30 b2e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e107
        have b2e3376 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have j0 := b2e50 X0 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e3377 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e3376 X0
             have i₂ := b2e228 X0 X0
             grind)
          | exact superpose b2e228 b2e3376
          | exact resolve b2e3376 b2e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3376
        have b2e3585 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op x x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e3377 (M.op X0 X1)
             have i₂ := b2e241 X0 X1
             grind)
          | exact superpose b2e241 b2e3377
          | exact resolve b2e3377 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3590 : (M.op (M.op x x) (M.op x x)) = (k (M.op x x) (M.op x x)) := by
          first
          | (have i₁ := b2e3377 (M.op x x)
             have i₂ := b2e35 x
             grind)
          | exact superpose b2e35 b2e3377
          | exact resolve b2e3377 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3601 : (M.op x (M.op x x)) = (k (M.op x x) (M.op x x)) := by
          first
          | (have i₁ := b2e3590
             have i₂ := b2e202 x x (M.op x x)
             grind)
          | exact superpose b2e202 b2e3590
          | exact resolve b2e3590 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3590
        have b2e3606 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (k (M.op x x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e3585 X0 X1
             have i₂ := b2e202 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b2e202 b2e3585
          | exact resolve b2e3585 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3585
        have b2e3613 : (M.op x x) = (k (M.op x x) (M.op x x)) := by
          first
          | (have i₁ := b2e3601
             have i₂ := b2e241 x x
             grind)
          | exact superpose b2e241 b2e3601
          | exact resolve b2e3601 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3601
        have b2e3618 : ∀ X0 X1 : G, (M.op x x) = (k (M.op x x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e3606 X0 X1
             have i₂ := b2e241 X0 X1
             grind)
          | exact superpose b2e241 b2e3606
          | exact resolve b2e3606 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3606
        have b2e4273 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e106 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106
        have b2e4274 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e4273
             have r₂ := b2e21
             grind)
          | exact resolve b2e4273 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4273
        have b2e4275 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e4274
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e4274
          | exact resolve b2e4274 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4274
        have b2e4276 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e4275
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e4275
          | exact resolve b2e4275 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e4275
        have b2e4277 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e4276
             grind)
          | exact superpose b2e4276 b2e21
          | exact resolve b2e21 b2e4276
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4406 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X4 X5) ∨ (M.op X2 X5) = (k X2 X5) ∨ (M.op X2 X5) = X2 ∨ (M.op X0 X4) = (k X0 X4) ∨ (M.op X0 X4) = X0 := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b2e99 X5 X4 X2 X3
             have i₂ := b2e99 X4 (M.op X2 X3) X0 X1
             grind)
          | (have i₁ := b2e99 X0 X1 X2 X3
             have i₂ := b2e99 X0 X1 X2 X3
             grind)
          | exact superpose b2e99 b2e99
          | (have j0 := b2e99 X5 X1 X2 X3
             have j1 := b2e99 X5 X1 X2 X3
             grind)
          | exact resolve b2e99 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4416 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = X3 ∨ (M.op X2 X3) = (k X2 X3) ∨ (M.op X2 X3) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e17 X2 X3
             have i₂ := b2e99 X2 X2 X0 X1
             grind)
          | (have i₁ := b2e17 (M.op X2 X3) X1
             have i₂ := b2e99 X0 (M.op X2 X3) X2 X3
             grind)
          | exact superpose b2e99 b2e17
          | (have j0 := b2e17 X2 X3
             have j1 := b2e99 X3 X1 X2 X3
             grind)
          | exact resolve b2e17 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4476 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op (M.op X0 X1) x) X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e3377 X2
             have i₂ := b2e99 X2 x X0 X1
             grind)
          | exact superpose b2e99 b2e3377
          | (have j1 := b2e99 X2 X1 X0 x
             grind)
          | exact resolve b2e3377 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4493 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X2 X2) (M.op X2 X2)) = (k X0 (M.op X2 X2)) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e48 X2 x X0
             have i₂ := b2e99 X1 X0 X2 x
             grind)
          | (have i₁ := b2e48 X0 X1 X0
             have i₂ := b2e99 X0 (M.op X0 X1) X2 x
             grind)
          | exact superpose b2e99 b2e48
          | (have j0 := b2e48 X2 X1 X0
             have j1 := b2e99 X1 X1 X2 x
             grind)
          | (have r₁ := b2e48 X0 X1 (M.op (M.op X2 x) (M.op X0 X1))
             have r₂ := b2e99 (M.op (M.op X2 x) (M.op X0 X1)) (M.op X0 X1) X2 x
             grind)
          | (have r₁ := b2e48 X0 X1 (M.op X0 X1)
             have r₂ := b2e99 (M.op X0 X1) X1 (M.op X0 X1) x
             grind)
          | exact resolve b2e48 b2e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e4507 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          grind
        have b2e4557 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e99 X1 X1 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4564 : ∀ X0 X1 : G, (M.op x X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e4557 X0 X1 x
             have i₂ := b2e202 X0 x X0
             grind)
          | exact superpose b2e202 b2e4557
          | (have j0 := b2e4557 X0 X1 x
             grind)
          | exact resolve b2e4557 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4557
        have b2e4603 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x X2)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4507 X0 X1 X2
             have i₂ := b2e202 X0 X1 X2
             grind)
          | exact superpose b2e202 b2e4507
          | (have j0 := b2e4507 X0 X1 X2
             grind)
          | exact resolve b2e4507 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4507
        have b2e4615 : ∀ X0 X1 X2 : G, (M.op x (M.op X2 X2)) = (k X0 (M.op X2 X2)) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4493 X0 X1 X2
             have i₂ := b2e202 X2 X2 (M.op X2 X2)
             grind)
          | exact superpose b2e202 b2e4493
          | (have j0 := b2e4493 X0 X1 X2
             grind)
          | (have r₁ := b2e4493 (M.op x X2) X2 X2
             have r₂ := b2e202 x X2 X2
             grind)
          | exact resolve b2e4493 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4493
        have b2e4623 : ∀ X0 X2 : G, (M.op X2 X2) = (k (M.op x x) X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X2
          first
          | (have i₁ := b2e4476 X0 x X2
             have i₂ := b2e202 X0 x x
             grind)
          | exact superpose b2e202 b2e4476
          | (have j0 := b2e4476 X0 x X2
             grind)
          | exact resolve b2e4476 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4476
        have b2e4671 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X3) = X2 ∨ (M.op x X2) = X3 ∨ (M.op X0 X2) = X0 := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e4416 X0 x X2 X3
             have i₂ := b2e202 X0 x X2
             grind)
          | exact superpose b2e202 b2e4416
          | (have j0 := b2e4416 X0 x X2 X3
             grind)
          | exact resolve b2e4416 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4416
        have b2e4677 : ∀ X0 X2 X3 X4 X5 : G, (M.op x (M.op X2 X3)) = (M.op X4 X5) ∨ (M.op X2 X5) = (k X2 X5) ∨ (M.op X2 X5) = X2 ∨ (M.op X0 X4) = (k X0 X4) ∨ (M.op X0 X4) = X0 := by
          intro X0 X2 X3 X4 X5
          first
          | (have i₁ := b2e4406 X0 x X2 X3 X4 X5
             have i₂ := b2e202 X0 x (M.op X2 X3)
             grind)
          | exact superpose b2e202 b2e4406
          | (have j0 := b2e4406 X2 x X2 X3 X5 X5
             grind)
          | exact resolve b2e4406 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4406
        have b2e4766 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op x (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op x X2)) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4603 X0 X1 X2
             have i₂ := b2e202 X0 X1 (M.op (M.op X0 X1) X2)
             grind)
          | exact superpose b2e202 b2e4603
          | (have j0 := b2e4603 X0 X1 X2
             grind)
          | exact resolve b2e4603 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4603
        have b2e4777 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op x x) = (k X0 (M.op X2 X2)) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4615 X0 X1 X2
             have i₂ := b2e241 X2 X2
             grind)
          | exact superpose b2e241 b2e4615
          | (have j0 := b2e4615 X0 X1 X2
             grind)
          | exact resolve b2e4615 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4615
        have b2e4812 : ∀ X0 X2 X4 X5 : G, (M.op x x) = (M.op X4 X5) ∨ (M.op X2 X5) = (k X2 X5) ∨ (M.op X0 X4) = (k X0 X4) ∨ (M.op X2 X5) = X2 ∨ (M.op X0 X4) = X0 := by
          intro X0 X2 X4 X5
          first
          | (have i₁ := b2e4677 X0 X2 x X4 X5
             have i₂ := b2e241 X2 x
             grind)
          | exact superpose b2e241 b2e4677
          | (have j0 := b2e4677 X2 X2 x X5 X5
             grind)
          | exact resolve b2e4677 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4677
        have b2e4858 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x X2)) ∨ (M.op X0 X1) = (M.op x x) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e4766 X0 X1 X2
             have i₂ := b2e241 (M.op X0 X1) X2
             grind)
          | exact superpose b2e241 b2e4766
          | (have j0 := b2e4766 X0 X1 X2
             grind)
          | exact resolve b2e4766 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4766
        have b2e5031 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e95 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e5032 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e95 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e5033 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e5031 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5031
        have b2e5598 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op X0 X1) ∨ (M.op (M.op X3 X4) X2) = (k (M.op X3 X4) X2) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X2) ∨ (M.op (M.op X3 X3) X0) = (k (M.op X3 X3) X0) ∨ (M.op X3 X3) = (M.op (M.op X3 X3) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e99 X2 X1 (M.op X3 X4) (M.op X3 X3)
             have i₂ := b2e100 X0 X3 X4
             grind)
          | (have i₁ := b2e99 X0 X1 X2 X3
             have i₂ := b2e100 (M.op X2 X3) X1 X2
             grind)
          | exact superpose b2e100 b2e99
          | (have j0 := b2e99 X2 X1 (M.op X3 X4) X3
             have j1 := b2e100 X0 X3 X2
             grind)
          | exact resolve b2e99 b2e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99 b2e100
        have b2e5621 : ∀ X0 X1 X2 X3 X4 : G, (M.op x X2) = (k (M.op X3 X4) X2) ∨ (M.op X1 X2) = (M.op X0 X1) ∨ (M.op X3 X4) = (M.op (M.op X3 X4) X2) ∨ (M.op (M.op X3 X3) X0) = (k (M.op X3 X3) X0) ∨ (M.op X3 X3) = (M.op (M.op X3 X3) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e5598 X0 X1 X2 X3 X4
             have i₂ := b2e202 X3 X4 X2
             grind)
          | exact superpose b2e202 b2e5598
          | (have j0 := b2e5598 X0 X1 X2 X3 X4
             grind)
          | exact resolve b2e5598 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5598
        have b2e5763 : ∀ X0 X1 X2 X3 X4 : G, (M.op x X2) = (M.op X3 X4) ∨ (M.op x X2) = (k (M.op X3 X4) X2) ∨ (M.op X1 X2) = (M.op X0 X1) ∨ (M.op (M.op X3 X3) X0) = (k (M.op X3 X3) X0) ∨ (M.op X3 X3) = (M.op (M.op X3 X3) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e5621 X0 X1 X2 X3 X4
             have i₂ := b2e202 X3 X4 X2
             grind)
          | exact superpose b2e202 b2e5621
          | (have j0 := b2e5621 X0 X1 X2 X3 X4
             grind)
          | exact resolve b2e5621 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5621
        have b2e5886 : ∀ X0 X1 X2 X3 X4 : G, (M.op x X0) = (k (M.op X3 X3) X0) ∨ (M.op x X2) = (M.op X3 X4) ∨ (M.op x X2) = (k (M.op X3 X4) X2) ∨ (M.op X1 X2) = (M.op X0 X1) ∨ (M.op X3 X3) = (M.op (M.op X3 X3) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e5763 X0 X1 X2 X3 X4
             have i₂ := b2e202 X3 X3 X0
             grind)
          | exact superpose b2e202 b2e5763
          | (have j0 := b2e5763 X0 X1 X2 X3 X4
             grind)
          | exact resolve b2e5763 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5763
        have b2e6006 : ∀ X0 X1 X2 X3 X4 : G, (M.op x X2) = (k (M.op X3 X4) X2) ∨ (M.op x X0) = (k (M.op X3 X3) X0) ∨ (M.op X1 X2) = (M.op X0 X1) ∨ (M.op x X2) = (M.op X3 X4) ∨ (M.op x X0) = (M.op X3 X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e5886 X0 X1 X2 X3 X4
             have i₂ := b2e202 X3 X3 X0
             grind)
          | exact superpose b2e202 b2e5886
          | (have j0 := b2e5886 X0 X1 X2 X3 X4
             grind)
          | exact resolve b2e5886 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5886
        have b2e8469 : x = (k x (M.op x (M.op x x))) ∨ x = (M.op x (M.op x (M.op x x))) := by
          first
          | (have i₁ := b2e56 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e56
          | exact resolve b2e56 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e8613 : x = (k x (M.op x x)) ∨ x = (M.op x (M.op x (M.op x x))) := by
          first
          | (have i₁ := b2e8469
             have i₂ := b2e241 x x
             grind)
          | exact superpose b2e241 b2e8469
          | exact resolve b2e8469 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8469
        have b2e8694 : x = (k x (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e8613
             have i₂ := b2e241 x (M.op x x)
             grind)
          | exact superpose b2e241 b2e8613
          | exact resolve b2e8613 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8613
        have b2e15084 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
          first
          | (have i₁ := b2e5033 (M.op x x)
             have i₂ := b2e3618 x x
             grind)
          | exact superpose b2e3618 b2e5033
          | (have j0 := b2e5033 (M.op x x)
             grind)
          | exact resolve b2e5033 b2e3618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5033
        have b2e15092 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
        clear b2e15084
        have b2e15176 : ∀ X0 : G, (M.op x X0) = (M.op X0 (σ (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b2e228 X0 (σ (M.op x x))
             have i₂ := b2e15092
             grind)
          | exact superpose b2e15092 b2e228
          | exact resolve b2e228 b2e15092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e15210 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
          intro X0
          first
          | (have i₁ := b2e202 (σ (M.op x x)) (σ (M.op x x)) X0
             have i₂ := b2e15092
             grind)
          | exact superpose b2e15092 b2e202
          | exact resolve b2e202 b2e15092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e15211 : (M.op x x) = (M.op x (σ (M.op x x))) := by
          first
          | (have i₁ := b2e241 (σ (M.op x x)) (σ (M.op x x))
             have i₂ := b2e15092
             grind)
          | exact superpose b2e15092 b2e241
          | exact resolve b2e241 b2e15092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e15517 : (σ (M.op x x)) = (M.op x (σ (M.op x x))) := by
          first
          | (have i₁ := b2e15092
             have i₂ := b2e15176 (σ (M.op x x))
             grind)
          | exact superpose b2e15176 b2e15092
          | exact resolve b2e15092 b2e15176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15092
        have b2e15529 : (M.op x x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e15517
             have i₂ := b2e15211
             grind)
          | exact superpose b2e15211 b2e15517
          | exact resolve b2e15517 b2e15211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15517
        have b2e17534 : (M.op x x) = (τ (M.op x x)) := by
          first
          | (have i₁ := b2e13 (M.op x x)
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e13
          | exact resolve b2e13 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17535 : ∀ X0 : G, (k (M.op x x) (σ X0)) = (σ (k (M.op x x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 (M.op x x) X0
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e18
          | exact resolve b2e18 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17538 : ∀ X0 X1 : G, (σ (k (M.op x x) (k (τ X0) X1))) = (k (M.op x x) (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X0 X1 (M.op x x)
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e28
          | exact resolve b2e28 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e17549 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (k (M.op x x) X0)) := by
          intro X0
          first
          | (have i₁ := b2e134 (M.op x x) X0
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e134
          | exact resolve b2e134 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17580 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op (M.op x x) X0) = (k (M.op x x) X0) ∨ (M.op x x) = (M.op (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e4564 (M.op x x) X0
             have i₂ := b2e35 x
             grind)
          | exact superpose b2e35 b2e4564
          | (have j0 := b2e4564 (M.op x x) X0
             grind)
          | (have r₁ := b2e4564 (M.op x x) x
             have r₂ := b2e35 x
             grind)
          | exact resolve b2e4564 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17586 : ∀ X0 : G, (M.op (M.op x x) X0) = (k (M.op x x) X0) ∨ (M.op x x) = (M.op (M.op x x) X0) := by
          intro X0
          first
          | (have j0 := b2e17580 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17580
        have b2e17592 : ∀ X0 : G, (M.op x X0) = (k (M.op x x) X0) ∨ (M.op x x) = (M.op (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e17586 X0
             have i₂ := b2e202 x x X0
             grind)
          | exact superpose b2e202 b2e17586
          | (have j0 := b2e17586 X0
             grind)
          | exact resolve b2e17586 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17586
        have b2e17611 : ∀ X0 : G, (M.op x X0) = (k (M.op x x) X0) ∨ (M.op x x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e17592 X0
             have i₂ := b2e202 x x X0
             grind)
          | exact superpose b2e202 b2e17592
          | (have j0 := b2e17592 X0
             grind)
          | exact resolve b2e17592 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17592
        have b2e24227 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e5032 (M.op x x) (M.op X0 X1)
             have i₂ := b2e3618 X0 X1
             grind)
          | exact superpose b2e3618 b2e5032
          | (have j0 := b2e5032 (M.op x x) (M.op X0 X1)
             grind)
          | exact resolve b2e5032 b2e3618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3618 b2e5032
        have b2e24262 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have j0 := b2e24227 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24227
        have b2e24286 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op x (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e24262 X0 X1
             have i₂ := b2e15176 (σ (M.op x x))
             grind)
          | exact superpose b2e15176 b2e24262
          | (have j0 := b2e24262 X0 X1
             grind)
          | exact resolve b2e24262 b2e15176
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15176 b2e24262
        have b2e24308 : ∀ X0 X1 : G, (M.op x x) = (σ (M.op X0 X1)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e24286 X0 X1
             have i₂ := b2e15211
             grind)
          | exact superpose b2e15211 b2e24286
          | (have j0 := b2e24286 X0 X1
             grind)
          | exact resolve b2e24286 b2e15211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15211 b2e24286
        have b2e24324 : ∀ X0 X1 : G, (σ (M.op x x)) = (M.op x (σ (M.op X0 X1))) ∨ (M.op x x) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e24308 X0 X1
             have i₂ := b2e15210 (σ (M.op X0 X1))
             grind)
          | exact superpose b2e15210 b2e24308
          | (have j0 := b2e24308 X0 X1
             grind)
          | exact resolve b2e24308 b2e15210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15210 b2e24308
        have b2e24337 : ∀ X0 X1 : G, (M.op x x) = (M.op x (σ (M.op X0 X1))) ∨ (M.op x x) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e24324 X0 X1
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e24324
          | (have j0 := b2e24324 X0 X1
             grind)
          | exact resolve b2e24324 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24324
        have b2e33167 : ∀ X0 : G, x ≠ x ∨ (M.op x x) = (k x (M.op X0 X0)) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e4777 x y X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4777
          | (have j0 := b2e4777 x y X0
             grind)
          | (have r₁ := b2e4777 x y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e4777 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4777
        have b2e33168 : ∀ X0 : G, (M.op x x) = (k x (M.op X0 X0)) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e33167 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33167
        have b2e37529 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k (M.op x x) X0)) ∨ (M.op x x) = (M.op x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e17535 X0
             have i₂ := b2e17611 (σ X0)
             grind)
          | exact superpose b2e17611 b2e17535
          | (have j1 := b2e17611 (σ X0)
             grind)
          | exact resolve b2e17535 b2e17611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17535
        have b2e44399 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e4671 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4671
        have b2e44400 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e44399 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44399
        have b2e44401 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e44400 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44400
        have b2e44503 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e44401 X0
             have j1 := b2e4564 X0 X0
             grind)
          | (have r₁ := b2e44401 x
             have r₂ := b2e4564 x x
             grind)
          | (have r₁ := b2e44401 X0
             have r₂ := b2e4564 X0 x
             grind)
          | exact resolve b2e44401 b2e4564
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44401
        have b2e44591 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e44503 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e44503 x
             have r₂ := b2e15 x x
             grind)
          | exact resolve b2e44503 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44503
        have b2e44711 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e44591 (σ X0)
             grind)
          | exact superpose b2e44591 b2e18
          | exact resolve b2e18 b2e44591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44719 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e137 X0 X0
             have i₂ := b2e44591 (τ X0)
             grind)
          | exact superpose b2e44591 b2e137
          | exact resolve b2e137 b2e44591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44721 : ∀ X0 X1 : G, (τ (M.op (k X0 (σ X1)) (k X0 (σ X1)))) = (k (k (τ X0) X1) (τ (k X0 (σ X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b2e1446 X0 X1 (k X0 (σ X1))
             have i₂ := b2e44591 (k X0 (σ X1))
             grind)
          | exact superpose b2e44591 b2e1446
          | exact resolve b2e1446 b2e44591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1446
        have b2e44730 : ∀ X0 X1 : G, (τ (M.op (k X0 (σ X1)) (k X0 (σ X1)))) = (k (k (τ X0) X1) (k (τ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e44721 X0 X1
             have i₂ := b2e30 X0 X1
             grind)
          | exact superpose b2e30 b2e44721
          | exact resolve b2e44721 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44721
        have b2e44732 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e44719 X0
             have i₂ := b2e44591 X0
             grind)
          | exact superpose b2e44591 b2e44719
          | exact resolve b2e44719 b2e44591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44719
        have b2e44740 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e44711 X0
             have i₂ := b2e44591 X0
             grind)
          | exact superpose b2e44591 b2e44711
          | exact resolve b2e44711 b2e44591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44711
        have b2e44762 : ∀ X0 X1 : G, (τ (M.op (k X0 (σ X1)) (k X0 (σ X1)))) = (M.op (k (τ X0) X1) (k (τ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e44730 X0 X1
             have i₂ := b2e44591 (k (τ X0) X1)
             grind)
          | exact superpose b2e44591 b2e44730
          | exact resolve b2e44730 b2e44591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44591 b2e44730
        have b2e45423 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e64 X0
             have i₂ := b2e44732 X0
             grind)
          | exact superpose b2e44732 b2e64
          | (have j0 := b2e64 X0
             grind)
          | exact resolve b2e64 b2e44732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e45598 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ X0) = (M.op x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e45423 X0
             have i₂ := b2e14 (M.op X0 X0)
             grind)
          | exact superpose b2e14 b2e45423
          | (have j0 := b2e45423 X0
             grind)
          | exact resolve b2e45423 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45423
        have b2e46455 : ∀ X0 X1 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e44740 (k (τ X0) X1)
             have i₂ := b2e25 X0 X1
             grind)
          | exact superpose b2e25 b2e44740
          | exact resolve b2e44740 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46520 : ∀ X0 X1 : G, (M.op x X1) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b2e228 X1 (σ X0)
             have i₂ := b2e44740 X0
             grind)
          | exact superpose b2e44740 b2e228
          | exact resolve b2e228 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46568 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (M.op X0 X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e202 (σ X0) (σ X0) X1
             have i₂ := b2e44740 X0
             grind)
          | exact superpose b2e44740 b2e202
          | exact resolve b2e202 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50596 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op X1 (σ X0)) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e46520 X2 X1
             have i₂ := b2e17 X2 X0
             grind)
          | (have i₁ := b2e46520 X0 X1
             have i₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e17 b2e46520
          | (have j1 := b2e17 X2 X0
             grind)
          | exact resolve b2e46520 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46520
        have b2e52565 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ x = (M.op x x) ∨ (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e4858 x y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4858
          | (have j0 := b2e4858 x x X0
             grind)
          | exact resolve b2e4858 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4858
        have b2e52754 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b2e52565 X0
             have j1 := b2e4564 x X0
             grind)
          | (have r₁ := b2e52565 X0
             have r₂ := b2e4564 x x
             grind)
          | (have r₁ := b2e52565 x
             have r₂ := b2e4564 x x
             grind)
          | exact resolve b2e52565 b2e4564
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4564 b2e52565
        have b2e64088 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op x x) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e4812 X0 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4812
        have b2e64089 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op x x) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e64088 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64088
        have b2e64090 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op x x) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e64089 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64089
        have b2e91782 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 (M.op (τ X0) (τ X0))
             have i₂ := b2e45598 (τ X0)
             grind)
          | exact superpose b2e45598 b2e25
          | (have j1 := b2e45598 (τ X0)
             grind)
          | exact resolve b2e25 b2e45598
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45598
        have b2e91854 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e91782 X0
             have i₂ := b2e44732 X0
             grind)
          | exact superpose b2e44732 b2e91782
          | (have j0 := b2e91782 X0
             grind)
          | exact resolve b2e91782 b2e44732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91782
        have b2e91985 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e91854 X0
             have i₂ := b2e14 (M.op X0 X0)
             grind)
          | exact superpose b2e14 b2e91854
          | (have j0 := b2e91854 X0
             grind)
          | exact resolve b2e91854 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91854
        have b2e92097 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (τ X0)) = (M.op x (τ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b2e91985 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e91985
          | (have j0 := b2e91985 X0
             grind)
          | exact resolve b2e91985 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91985
        have b2e123108 : ∀ X0 X1 X2 : G, (M.op x X1) ≠ (M.op x X1) ∨ (M.op x X1) = (k (M.op X0 X0) X1) ∨ (M.op X1 X2) = (M.op X2 X1) ∨ (M.op X0 X0) = (M.op x X1) ∨ (M.op X0 X0) = (M.op x X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e6006 X1 X2 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6006
        have b2e123113 : ∀ X0 X1 X2 : G, (M.op x X1) ≠ (M.op x X1) ∨ (M.op x X1) = (k (M.op X0 X0) X1) ∨ (M.op X1 X2) = (M.op X2 X1) ∨ (M.op X0 X0) = (M.op x X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e123108 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123108
        have b2e123114 : ∀ X0 X1 X2 : G, (M.op x X1) = (k (M.op X0 X0) X1) ∨ (M.op X1 X2) = (M.op X2 X1) ∨ (M.op X0 X0) = (M.op x X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e123113 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123113
        have b2e129732 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ (τ (τ X0))) = (M.op x (τ (τ (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 (M.op (τ X0) (τ X0))
             have i₂ := b2e92097 (τ X0)
             grind)
          | exact superpose b2e92097 b2e25
          | (have j1 := b2e92097 (τ X0)
             grind)
          | exact resolve b2e25 b2e92097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e92097
        have b2e129759 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (τ (τ (τ X0))) = (M.op x (τ (τ (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e129732 X0
             have i₂ := b2e44732 X0
             grind)
          | exact superpose b2e44732 b2e129732
          | (have j0 := b2e129732 X0
             grind)
          | exact resolve b2e129732 b2e44732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129732
        have b2e129832 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (τ (τ (τ X0))) = (M.op x (τ (τ (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e129759 X0
             have i₂ := b2e14 (M.op X0 X0)
             grind)
          | exact superpose b2e14 b2e129759
          | (have j0 := b2e129759 X0
             grind)
          | exact resolve b2e129759 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129759
        have b2e129887 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (τ (τ X0))) = (M.op x (τ (τ (τ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e129832 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e129832
          | (have j0 := b2e129832 X0
             grind)
          | exact resolve b2e129832 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129832
        have b2e152893 : x = (k x (M.op x x)) ∨ (M.op x x) = (k x (M.op x x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e52754 (M.op x x)
             have i₂ := b2e35 x
             grind)
          | exact superpose b2e35 b2e52754
          | (have j0 := b2e52754 x
             grind)
          | exact resolve b2e52754 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e52754
        have b2e152935 : (M.op x x) = (k x (M.op x x)) ∨ x = (k x (M.op x x)) := by
          first
          | (have j1 := b2e53 x
             grind)
          | (have r₁ := b2e152893
             have r₂ := b2e53 x
             grind)
          | exact resolve b2e152893 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e152893
        have b2e153016 : x ≠ (M.op x x) ∨ x = (k x (M.op x x)) := by grind
        clear b2e152935
        have b2e153027 : x = (k x (M.op x x)) := by
          first
          | (have r₁ := b2e153016
             have r₂ := b2e8694
             grind)
          | exact resolve b2e153016 b2e8694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8694 b2e153016
        have b2e159096 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (M.op (M.op x x) X0)) ∨ (M.op X0 X0) = (k (M.op x x) X0) ∨ (M.op x x) = (M.op (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e17549 X0
             have i₂ := b2e4623 (M.op x x) X0
             grind)
          | exact superpose b2e4623 b2e17549
          | (have j1 := b2e4623 (M.op x x) X0
             grind)
          | exact resolve b2e17549 b2e4623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e159120 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (M.op (M.op x x) X0)) ∨ (M.op X0 X0) = (k (M.op x x) X0) := by
          intro X0
          first
          | (have j0 := b2e159096 X0
             have j1 := b2e15 (M.op x x) X0
             grind)
          | (have r₁ := b2e159096 x
             have r₂ := b2e15 (M.op x x) x
             grind)
          | exact resolve b2e159096 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159096
        have b2e159201 : ∀ X0 : G, (τ (M.op x X0)) = (k (M.op x x) (τ X0)) ∨ (M.op X0 X0) = (k (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e159120 X0
             have i₂ := b2e202 x x X0
             grind)
          | exact superpose b2e202 b2e159120
          | (have j0 := b2e159120 X0
             grind)
          | exact resolve b2e159120 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e159120
        have b2e163048 : ∀ X0 X1 : G, (M.op x x) = (k x (M.op x (M.op X0 X1))) ∨ (M.op (M.op X0 X1) y) = (k (M.op X0 X1) y) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e33168 (M.op X0 X1)
             have i₂ := b2e202 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b2e202 b2e33168
          | (have j0 := b2e33168 (M.op X0 X1)
             grind)
          | exact resolve b2e33168 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33168
        have b2e163130 : ∀ X0 X1 : G, (M.op x x) = (k x (M.op x x)) ∨ (M.op (M.op X0 X1) y) = (k (M.op X0 X1) y) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e163048 X0 X1
             have i₂ := b2e241 X0 X1
             grind)
          | exact superpose b2e241 b2e163048
          | (have j0 := b2e163048 X0 X1
             grind)
          | exact resolve b2e163048 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163048
        have b2e163137 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op (M.op X0 X1) y) = (k (M.op X0 X1) y) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e163130 X0 X1
             have i₂ := b2e153027
             grind)
          | exact superpose b2e153027 b2e163130
          | (have j0 := b2e163130 X0 X1
             grind)
          | exact resolve b2e163130 b2e153027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e153027 b2e163130
        have b2e163143 : ∀ X0 X1 : G, (M.op x y) = (k (M.op X0 X1) y) ∨ x = (M.op x x) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e163137 X0 X1
             have i₂ := b2e202 X0 X1 y
             grind)
          | exact superpose b2e202 b2e163137
          | (have j0 := b2e163137 X0 X1
             grind)
          | exact resolve b2e163137 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163137
        have b2e163149 : ∀ X0 X1 : G, x = (k (M.op X0 X1) y) ∨ x = (M.op x x) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e163143 X0 X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e163143
          | (have j0 := b2e163143 X0 X1
             grind)
          | exact resolve b2e163143 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163143
        have b2e163155 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x y) ∨ x = (k (M.op X0 X1) y) ∨ x = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b2e163149 X0 X1
             have i₂ := b2e202 X0 X1 y
             grind)
          | exact superpose b2e202 b2e163149
          | (have j0 := b2e163149 X0 X1
             grind)
          | exact resolve b2e163149 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163149
        have b2e163161 : ∀ X0 X1 : G, x = (k (M.op X0 X1) y) ∨ (M.op X0 X1) = x ∨ x = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b2e163155 X0 X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e163155
          | (have j0 := b2e163155 X0 X1
             grind)
          | exact resolve b2e163155 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163155
        have b2e163901 : ∀ X0 : G, x = (k (σ (M.op X0 X0)) y) ∨ x = (σ (M.op X0 X0)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e163161 (σ X0) (σ X0)
             have i₂ := b2e44740 X0
             grind)
          | exact superpose b2e44740 b2e163161
          | (have j0 := b2e163161 x x
             grind)
          | exact resolve b2e163161 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163161
        have b2e166250 : (M.op x x) = (M.op x (σ x)) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e24337 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e24337
          | exact resolve b2e24337 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24337
        have b2e166376 : (τ (M.op x x)) = (k (τ x) x) ∨ (σ x) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e141 x x
             have i₂ := b2e166250
             grind)
          | exact superpose b2e166250 b2e141
          | (have j0 := b2e141 x x
             grind)
          | exact resolve b2e141 b2e166250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e141
        have b2e166378 : x ≠ (M.op x x) ∨ (M.op (σ x) (σ x)) = (k x (σ x)) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e15 x (σ x)
             have i₂ := b2e166250
             grind)
          | exact superpose b2e166250 b2e15
          | (have j0 := b2e15 x x
             grind)
          | exact resolve b2e15 b2e166250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166250
        have b2e166432 : (τ (M.op x x)) = (k (τ x) x) ∨ (σ x) = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b2e166376
        have b2e166433 : (σ (M.op x x)) = (k x (σ x)) ∨ x ≠ (M.op x x) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e166378
             have i₂ := b2e44740 x
             grind)
          | exact superpose b2e44740 b2e166378
          | exact resolve b2e166378 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166378
        have b2e166434 : (M.op x x) = (k (τ x) x) ∨ (σ x) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e166432
             have i₂ := b2e17534
             grind)
          | exact superpose b2e17534 b2e166432
          | exact resolve b2e166432 b2e17534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166432
        have b2e166440 : x ≠ (M.op x x) ∨ (M.op x x) = (k x (σ x)) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e166433
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e166433
          | exact resolve b2e166433 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166433
        have b2e171451 : ∀ X0 : G, (M.op x x) = (M.op x (τ (τ (τ X0)))) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e241 x (τ (τ (τ X0)))
             have i₂ := b2e129887 X0
             grind)
          | exact superpose b2e129887 b2e241
          | (have j1 := b2e129887 X0
             grind)
          | exact resolve b2e241 b2e129887
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e172601 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 x) X0) ∨ (M.op x x) = (k (M.op X1 X1) x) ∨ (M.op X1 X1) = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b2e3377 X0
             have i₂ := b2e123114 X1 x X0
             grind)
          | (have i₁ := b2e3377 X1
             have i₂ := b2e123114 X0 X1 x
             grind)
          | exact superpose b2e123114 b2e3377
          | (have j1 := b2e123114 X1 x x
             grind)
          | exact resolve b2e3377 b2e123114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123114
        have b2e172678 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 x) X0) ∨ (M.op x x) = (k (M.op X1 X1) x) := by
          intro X0 X1
          first
          | (have j0 := b2e172601 X0 X1
             have j1 := b2e236 X0 X0 x
             grind)
          | (have r₁ := b2e172601 X0 x
             have r₂ := b2e236 x x x
             grind)
          | (have r₁ := b2e172601 X0 x
             have r₂ := b2e236 x x x
             grind)
          | exact resolve b2e172601 b2e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e236 b2e172601
        have b2e180114 : ∀ X0 : G, (M.op x x) = (τ (τ (τ X0))) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e129887 X0
             have i₂ := b2e171451 X0
             grind)
          | exact superpose b2e171451 b2e129887
          | (have j0 := b2e129887 X0
             have j1 := b2e171451 X0
             grind)
          | exact resolve b2e129887 b2e171451
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129887 b2e171451
        have b2e180198 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op x x) = (τ (τ (τ X0))) := by
          intro X0
          first
          | (have j0 := b2e180114 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180114
        have b2e180553 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op x x) = (τ (τ (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e134 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e180198 (σ X0)
             grind)
          | exact superpose b2e180198 b2e134
          | (have j1 := b2e180198 (σ X0)
             grind)
          | exact resolve b2e134 b2e180198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180198
        have b2e180565 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (M.op x x) = (τ (τ (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e180553 X0
             have i₂ := b2e44740 X0
             grind)
          | exact superpose b2e44740 b2e180553
          | (have j0 := b2e180553 X0
             grind)
          | exact resolve b2e180553 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180553
        have b2e180599 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op x x) = (τ (τ (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e180565 X0
             have i₂ := b2e13 (M.op X0 X0)
             grind)
          | exact superpose b2e13 b2e180565
          | (have j0 := b2e180565 X0
             grind)
          | exact resolve b2e180565 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180565
        have b2e180623 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op x x) = (τ (τ (τ (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b2e180599 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e180599
          | (have j0 := b2e180599 X0
             grind)
          | exact resolve b2e180599 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180599
        have b2e180631 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op x x) = (τ (τ X0)) := by
          intro X0
          first
          | (have i₁ := b2e180623 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e180623
          | (have j0 := b2e180623 X0
             grind)
          | exact resolve b2e180623 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180623
        have b2e180693 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (M.op x x) = (τ (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e134 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e180631 (σ X0)
             grind)
          | exact superpose b2e180631 b2e134
          | (have j1 := b2e180631 (σ X0)
             grind)
          | exact resolve b2e134 b2e180631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180631
        have b2e180708 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (M.op x x) = (τ (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e180693 X0
             have i₂ := b2e44740 X0
             grind)
          | exact superpose b2e44740 b2e180693
          | (have j0 := b2e180693 X0
             grind)
          | exact resolve b2e180693 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180693
        have b2e180744 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (M.op x x) = (τ (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e180708 X0
             have i₂ := b2e13 (M.op X0 X0)
             grind)
          | exact superpose b2e13 b2e180708
          | (have j0 := b2e180708 X0
             grind)
          | exact resolve b2e180708 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180708
        have b2e180768 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op x x) = (τ (τ (σ X0))) := by
          intro X0
          first
          | (have i₁ := b2e180744 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e180744
          | (have j0 := b2e180744 X0
             grind)
          | exact resolve b2e180744 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180744
        have b2e180776 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ X0) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e180768 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e180768
          | (have j0 := b2e180768 X0
             grind)
          | exact resolve b2e180768 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180768
        have b2e180914 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e134 X0 (M.op (σ X0) (σ X0))
             have i₂ := b2e180776 (σ X0)
             grind)
          | exact superpose b2e180776 b2e134
          | (have j1 := b2e180776 (σ X0)
             grind)
          | exact resolve b2e134 b2e180776
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180776
        have b2e180929 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (τ (σ X0)) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e180914 X0
             have i₂ := b2e44740 X0
             grind)
          | exact superpose b2e44740 b2e180914
          | (have j0 := b2e180914 X0
             grind)
          | exact resolve b2e180914 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180914
        have b2e180963 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (τ (σ X0)) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e180929 X0
             have i₂ := b2e13 (M.op X0 X0)
             grind)
          | exact superpose b2e13 b2e180929
          | (have j0 := b2e180929 X0
             grind)
          | exact resolve b2e180929 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180929
        have b2e180985 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e180963 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e180963
          | (have j0 := b2e180963 X0
             grind)
          | exact resolve b2e180963 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180963
        have b2e180993 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op x x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e180985 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e180985
          | (have j0 := b2e180985 X0
             grind)
          | exact resolve b2e180985 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180985
        have b2e181153 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e180993 (σ X0)
             have i₂ := b2e44740 X0
             grind)
          | exact superpose b2e44740 b2e180993
          | (have j0 := b2e180993 (σ X0)
             grind)
          | exact resolve b2e180993 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180993
        have b2e181245 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e181153 X0
             have i₂ := b2e18 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e18 b2e181153
          | (have j0 := b2e181153 X0
             grind)
          | exact resolve b2e181153 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e181153
        have b2e197200 : ∀ X0 X1 : G, (M.op x x) = (k (τ (M.op X0 X0)) x) ∨ (M.op X1 X1) = (k (M.op X1 x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e172678 X1 (τ X0)
             have i₂ := b2e44732 X0
             grind)
          | exact superpose b2e44732 b2e172678
          | (have j0 := b2e172678 X1 X1
             grind)
          | exact resolve b2e172678 b2e44732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e172678
        have b2e232844 : ∀ X0 : G, (τ x) = (k (M.op X0 X0) (τ y)) ∨ x = (σ (M.op X0 X0)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e134 (M.op X0 X0) y
             have i₂ := b2e163901 X0
             grind)
          | exact superpose b2e163901 b2e134
          | (have j1 := b2e163901 X0
             grind)
          | exact resolve b2e134 b2e163901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163901
        have b2e233272 : ∀ X0 X1 : G, (σ (M.op x x)) = (k (M.op X0 X0) (σ x)) ∨ (M.op X1 X1) = (k (M.op X1 x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e25 (M.op X0 X0) x
             have i₂ := b2e197200 X0 X1
             grind)
          | exact superpose b2e197200 b2e25
          | (have j1 := b2e197200 X0 X1
             grind)
          | exact resolve b2e25 b2e197200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e197200
        have b2e233279 : ∀ X0 X1 : G, (M.op x x) = (k (M.op X0 X0) (σ x)) ∨ (M.op X1 X1) = (k (M.op X1 x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e233272 X0 X1
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e233272
          | (have j0 := b2e233272 X0 X1
             grind)
          | exact resolve b2e233272 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e233272
        have b2e234266 : ∀ X0 : G, (M.op x x) = (M.op x (σ x)) ∨ (M.op x x) = (M.op x (σ x)) ∨ (M.op X0 X0) = (k (M.op X0 x) X0) := by
          intro X0
          first
          | (have i₁ := b2e17611 (σ x)
             have i₂ := b2e233279 x X0
             grind)
          | exact superpose b2e233279 b2e17611
          | (have j0 := b2e17611 (σ x)
             have j1 := b2e233279 X0 X0
             grind)
          | exact resolve b2e17611 b2e233279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e233279
        have b2e234276 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 x) X0) ∨ (M.op x x) = (M.op x (σ x)) := by
          intro X0
          first
          | (have j0 := b2e234266 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234266
        have b2e234475 : (σ (M.op x x)) = (k x (σ x)) ∨ (σ x) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e25 x x
             have i₂ := b2e166434
             grind)
          | exact superpose b2e166434 b2e25
          | exact resolve b2e25 b2e166434
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166434
        have b2e234476 : (M.op x x) = (k x (σ x)) ∨ (σ x) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e234475
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e234475
          | exact resolve b2e234475 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234475
        have b2e234477 : (M.op x x) = (k x (σ x)) ∨ (σ x) = (M.op x x) := by
          first
          | (have r₁ := b2e234476
             have r₂ := b2e166440
             grind)
          | exact resolve b2e234476 b2e166440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e166440 b2e234476
        have b2e234506 : (τ (M.op x x)) = (k (τ x) x) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e30 x x
             have i₂ := b2e234477
             grind)
          | exact superpose b2e234477 b2e30
          | exact resolve b2e30 b2e234477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e234537 : (M.op x x) = (k (τ x) x) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e234506
             have i₂ := b2e17534
             grind)
          | exact superpose b2e17534 b2e234506
          | exact resolve b2e234506 b2e17534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234506
        have b2e234555 : (σ (k (M.op x x) (M.op x x))) = (k (M.op x x) (k x (σ x))) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e17538 x x
             have i₂ := b2e234537
             grind)
          | exact superpose b2e234537 b2e17538
          | exact resolve b2e17538 b2e234537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17538 b2e234537
        have b2e234562 : (σ (M.op x x)) = (k (M.op x x) (k x (σ x))) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e234555
             have i₂ := b2e3613
             grind)
          | exact superpose b2e3613 b2e234555
          | exact resolve b2e234555 b2e3613
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3613 b2e234555
        have b2e234573 : (M.op x x) = (k (M.op x x) (k x (σ x))) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e234562
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e234562
          | exact resolve b2e234562 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234562
        have b2e234586 : (M.op x x) = (M.op x (k x (σ x))) ∨ (M.op x x) = (M.op x (k x (σ x))) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e17611 (k x (σ x))
             have i₂ := b2e234573
             grind)
          | exact superpose b2e234573 b2e17611
          | (have j0 := b2e17611 (k x (σ x))
             grind)
          | exact resolve b2e17611 b2e234573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17611 b2e234573
        have b2e234588 : (M.op x x) = (M.op x (k x (σ x))) ∨ (σ x) = (M.op x x) := by grind
        clear b2e234586
        have b2e234604 : ∀ X0 : G, (M.op x x) ≠ (k x (σ x)) ∨ (M.op x x) = (k (k x (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e435 X0 (k x (σ x))
             have i₂ := b2e234588
             grind)
          | exact superpose b2e234588 b2e435
          | (have j0 := b2e435 X0 (k x (σ x))
             grind)
          | exact resolve b2e435 b2e234588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e435 b2e234588
        have b2e234706 : ∀ X0 : G, (M.op x x) = (k (k x (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op x x) := by
          intro X0
          first
          | (have j0 := b2e234604 X0
             grind)
          | (have r₁ := b2e234604 X0
             have r₂ := b2e234477
             grind)
          | exact resolve b2e234604 b2e234477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234477 b2e234604
        have b2e235018 : (σ (M.op x x)) = (σ (k x (σ x))) ∨ (M.op x x) = (σ (k x (σ x))) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e181245 (k x (σ x))
             have i₂ := b2e234706 (k x (σ x))
             grind)
          | exact superpose b2e234706 b2e181245
          | (have j0 := b2e181245 (k x (σ x))
             grind)
          | exact resolve b2e181245 b2e234706
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e181245 b2e234706
        have b2e235079 : (M.op x x) = (σ (k x (σ x))) ∨ (M.op x x) = (σ (k x (σ x))) ∨ (σ x) = (M.op x x) := by
          first
          | (have i₁ := b2e235018
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e235018
          | exact resolve b2e235018 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e235018
        have b2e235080 : (M.op x x) = (σ (k x (σ x))) ∨ (σ x) = (M.op x x) := by grind
        clear b2e235079
        have b2e238251 : (M.op x (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op x (σ x)) ∨ (M.op x x) = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e37529 x
             have i₂ := b2e234276 x
             grind)
          | exact superpose b2e234276 b2e37529
          | (have j0 := b2e37529 x
             grind)
          | exact resolve b2e37529 b2e234276
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37529 b2e234276
        have b2e238285 : (M.op x (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op x (σ x)) := by grind
        clear b2e238251
        have b2e238294 : (M.op x x) = (M.op x (σ x)) ∨ (M.op x x) = (M.op x (σ x)) := by
          first
          | (have i₁ := b2e238285
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e238285
          | exact resolve b2e238285 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238285
        have b2e238295 : (M.op x x) = (M.op x (σ x)) := by grind
        clear b2e238294
        have b2e238380 : (τ (M.op x x)) = (k (τ x) x) ∨ x = (M.op x x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e3094 x x
             have i₂ := b2e238295
             grind)
          | exact superpose b2e238295 b2e3094
          | (have j0 := b2e3094 x x
             grind)
          | exact resolve b2e3094 b2e238295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3094
        have b2e238391 : x ≠ (M.op x x) ∨ (M.op (σ x) (σ x)) = (k x (σ x)) := by
          first
          | (have i₁ := b2e15 x (σ x)
             have i₂ := b2e238295
             grind)
          | exact superpose b2e238295 b2e15
          | (have j0 := b2e15 x x
             grind)
          | exact resolve b2e15 b2e238295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e238511 : (σ (M.op x x)) = (k x (σ x)) ∨ x ≠ (M.op x x) := by
          first
          | (have i₁ := b2e238391
             have i₂ := b2e44740 x
             grind)
          | exact superpose b2e44740 b2e238391
          | exact resolve b2e238391 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238391
        have b2e238519 : (M.op x x) = (k (τ x) x) ∨ x = (M.op x x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e238380
             have i₂ := b2e17534
             grind)
          | exact superpose b2e17534 b2e238380
          | exact resolve b2e238380 b2e17534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238380
        have b2e238536 : x ≠ (M.op x x) ∨ (M.op x x) = (k x (σ x)) := by
          first
          | (have i₁ := b2e238511
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e238511
          | exact resolve b2e238511 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238511
        have b2e243561 : (σ (M.op x x)) = (k x (σ x)) ∨ x = (M.op x x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e25 x x
             have i₂ := b2e238519
             grind)
          | exact superpose b2e238519 b2e25
          | exact resolve b2e25 b2e238519
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238519
        have b2e243562 : (M.op x x) = (k x (σ x)) ∨ x = (M.op x x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e243561
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e243561
          | exact resolve b2e243561 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e243561
        have b2e243563 : (M.op x x) = (k x (σ x)) ∨ x = (k x (σ x)) := by
          first
          | (have r₁ := b2e243562
             have r₂ := b2e238536
             grind)
          | exact resolve b2e243562 b2e238536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238536 b2e243562
        have b2e243599 : x ≠ (M.op x x) ∨ x = (k x (σ x)) := by grind
        have b2e243629 : ∀ X0 X1 : G, (M.op X0 X0) ≠ x ∨ x = (k x (σ x)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e243599
             have i₂ := b2e64090 X1 X0
             grind)
          | (have i₁ := b2e243599
             have i₂ := b2e64090 X0 x
             grind)
          | exact superpose b2e64090 b2e243599
          | (have j1 := b2e64090 X1 X0
             grind)
          | (have r₁ := b2e243599
             have r₂ := b2e64090 x x
             grind)
          | exact resolve b2e243599 b2e64090
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64090
        have b2e271811 : (τ (M.op (M.op x x) (M.op x x))) = (M.op (k (τ x) x) (k (τ x) x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e44762 x x
             have i₂ := b2e243563
             grind)
          | exact superpose b2e243563 b2e44762
          | exact resolve b2e44762 b2e243563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44762 b2e243563
        have b2e271890 : (τ (M.op x (M.op x x))) = (M.op (k (τ x) x) (k (τ x) x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e271811
             have i₂ := b2e202 x x (M.op x x)
             grind)
          | exact superpose b2e202 b2e271811
          | exact resolve b2e271811 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e271811
        have b2e271897 : (τ (M.op x x)) = (M.op (k (τ x) x) (k (τ x) x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e271890
             have i₂ := b2e241 x x
             grind)
          | exact superpose b2e241 b2e271890
          | exact resolve b2e271890 b2e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e241 b2e271890
        have b2e271901 : (M.op x x) = (M.op (k (τ x) x) (k (τ x) x)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e271897
             have i₂ := b2e17534
             grind)
          | exact superpose b2e17534 b2e271897
          | exact resolve b2e271897 b2e17534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e271897
        have b2e272875 : (σ (M.op x x)) = (M.op (k x (σ x)) (k x (σ x))) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e46455 x x
             have i₂ := b2e271901
             grind)
          | exact superpose b2e271901 b2e46455
          | exact resolve b2e46455 b2e271901
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46455 b2e271901
        have b2e272915 : (M.op x x) = (M.op (k x (σ x)) (k x (σ x))) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e272875
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e272875
          | exact resolve b2e272875 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e272875
        have b2e275747 : ∀ X0 : G, (σ x) ≠ (M.op x (σ x)) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e50596 y (σ x) X0
             grind)
          | exact superpose b2e50596 b2e21
          | (have j1 := b2e50596 y x X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e50596 (σ y) x (σ x)
             grind)
          | exact resolve b2e21 b2e50596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50596
        have b2e275801 : ∀ X0 : G, (σ x) ≠ (M.op x x) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e275747 X0
             have i₂ := b2e238295
             grind)
          | exact superpose b2e238295 b2e275747
          | (have j0 := b2e275747 X0
             grind)
          | exact resolve b2e275747 b2e238295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e238295 b2e275747
        have b2e276877 : ∀ X0 : G, (τ x) = (k (τ (M.op X0 X0)) (τ y)) ∨ x = (σ (τ (M.op X0 X0))) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e232844 (τ X0)
             have i₂ := b2e44732 X0
             grind)
          | exact superpose b2e44732 b2e232844
          | exact resolve b2e232844 b2e44732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e232844
        have b2e276916 : ∀ X0 : G, (τ x) = (τ (k (M.op X0 X0) y)) ∨ x = (σ (τ (M.op X0 X0))) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e276877 X0
             have i₂ := b2e137 y (M.op X0 X0)
             grind)
          | exact superpose b2e137 b2e276877
          | (have j0 := b2e276877 X0
             grind)
          | exact resolve b2e276877 b2e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137 b2e276877
        have b2e276930 : ∀ X0 : G, (τ x) = (τ (k (M.op X0 X0) y)) ∨ (M.op X0 X0) = x ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e276916 X0
             have i₂ := b2e14 (M.op X0 X0)
             grind)
          | exact superpose b2e14 b2e276916
          | (have j0 := b2e276916 X0
             grind)
          | exact resolve b2e276916 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e276916
        have b2e276976 : (τ x) = (τ (k (M.op x x) y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e276930 (k x (σ x))
             have i₂ := b2e272915
             grind)
          | exact superpose b2e272915 b2e276930
          | (have j0 := b2e276930 x
             grind)
          | exact resolve b2e276930 b2e272915
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e272915 b2e276930
        have b2e277000 : (τ x) = (τ (k (M.op x x) y)) ∨ x = (M.op x x) ∨ x = (k x (σ x)) := by grind
        clear b2e276976
        have b2e277021 : (τ x) = (τ (k (M.op x x) y)) ∨ x = (k x (σ x)) := by
          first
          | (have r₁ := b2e277000
             have r₂ := b2e243599
             grind)
          | exact resolve b2e277000 b2e243599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e243599 b2e277000
        have b2e277063 : (τ x) = (k (M.op x x) (τ y)) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e277021
             have i₂ := b2e17549 y
             grind)
          | exact superpose b2e17549 b2e277021
          | exact resolve b2e277021 b2e17549
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17549 b2e277021
        have b2e277129 : (σ (τ x)) = (k (σ (M.op x x)) y) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e26 y (M.op x x)
             have i₂ := b2e277063
             grind)
          | exact superpose b2e277063 b2e26
          | exact resolve b2e26 b2e277063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277063
        have b2e277160 : (σ (τ x)) = (k (M.op x x) y) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e277129
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e277129
          | exact resolve b2e277129 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277129
        have b2e277186 : x = (k (M.op x x) y) ∨ x = (k x (σ x)) := by
          first
          | (have i₁ := b2e277160
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e277160
          | exact resolve b2e277160 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277160
        have b2e277225 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 ∨ x = (k x (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e4623 X0 y
             have i₂ := b2e277186
             grind)
          | exact superpose b2e277186 b2e4623
          | (have j0 := b2e4623 X0 y
             grind)
          | exact resolve b2e4623 b2e277186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4623 b2e277186
        have b2e277254 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ x = (k x (σ x)) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e277225 X0
             have j1 := b2e243629 y X0
             grind)
          | (have r₁ := b2e277225 X0
             have r₂ := b2e243629 y x
             grind)
          | exact resolve b2e277225 b2e243629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e243629 b2e277225
        have b2e277332 : ∀ X0 : G, (σ x) = (M.op x x) ∨ (σ x) = (M.op x x) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e235080
             have i₂ := b2e277254 X0
             grind)
          | exact superpose b2e277254 b2e235080
          | (have j1 := b2e277254 X0
             grind)
          | exact resolve b2e235080 b2e277254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e235080 b2e277254
        have b2e277347 : ∀ X0 : G, (σ x) = (M.op x x) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e277332 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277332
        have b2e277354 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e277347 X0
             have j1 := b2e275801 X0
             grind)
          | (have r₁ := b2e277347 X0
             have r₂ := b2e275801 X0
             grind)
          | exact resolve b2e277347 b2e275801
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e275801 b2e277347
        have b2e277433 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op (σ X0) y)) ∨ (σ X0) = (M.op (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b2e134 X0 y
             have i₂ := b2e277354 (σ X0)
             grind)
          | exact superpose b2e277354 b2e134
          | (have j1 := b2e277354 (σ X0)
             grind)
          | exact resolve b2e134 b2e277354
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e134
        have b2e277440 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (τ X0) y) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 y
             have i₂ := b2e277354 (τ X0)
             grind)
          | exact superpose b2e277354 b2e25
          | (have j1 := b2e277354 (τ X0)
             grind)
          | exact resolve b2e25 b2e277354
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277354
        have b2e277562 : ∀ X0 : G, (τ (M.op x y)) = (k (M.op X0 X0) (τ y)) ∨ (M.op x y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e277433 (M.op X0 X0)
             have i₂ := b2e46568 X0 y
             grind)
          | exact superpose b2e46568 b2e277433
          | exact resolve b2e277433 b2e46568
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46568 b2e277433
        have b2e277611 : ∀ X0 : G, (τ x) = (k (M.op X0 X0) (τ y)) ∨ (M.op x y) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e277562 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e277562
          | (have j0 := b2e277562 X0
             grind)
          | exact resolve b2e277562 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277562
        have b2e277625 : ∀ X0 : G, (τ x) = (k (M.op X0 X0) (τ y)) ∨ x = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e277611 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e277611
          | (have j0 := b2e277611 X0
             grind)
          | exact resolve b2e277611 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277611
        have b2e277857 : ∀ X0 : G, (σ (τ x)) = (k (σ (M.op X0 X0)) y) ∨ x = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e26 y (M.op X0 X0)
             have i₂ := b2e277625 X0
             grind)
          | exact superpose b2e277625 b2e26
          | (have j1 := b2e277625 X0
             grind)
          | exact resolve b2e26 b2e277625
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277625
        have b2e277888 : ∀ X0 : G, x = (k (σ (M.op X0 X0)) y) ∨ x = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e277857 X0
             have i₂ := b2e14 x
             grind)
          | exact superpose b2e14 b2e277857
          | (have j0 := b2e277857 X0
             grind)
          | exact resolve b2e277857 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277857
        have b2e278104 : ∀ X0 : G, x = (k (σ (τ (M.op X0 X0))) y) ∨ x = (σ (τ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e277888 (τ X0)
             have i₂ := b2e44732 X0
             grind)
          | exact superpose b2e44732 b2e277888
          | exact resolve b2e277888 b2e44732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277888
        have b2e278163 : ∀ X0 : G, x = (k (M.op X0 X0) y) ∨ x = (σ (τ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e278104 X0
             have i₂ := b2e14 (M.op X0 X0)
             grind)
          | exact superpose b2e14 b2e278104
          | (have j0 := b2e278104 X0
             grind)
          | exact resolve b2e278104 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e278104
        have b2e278204 : ∀ X0 : G, x = (k (M.op X0 X0) y) ∨ (M.op X0 X0) = x := by
          intro X0
          first
          | (have i₁ := b2e278163 X0
             have i₂ := b2e14 (M.op X0 X0)
             grind)
          | exact superpose b2e14 b2e278163
          | (have j0 := b2e278163 X0
             grind)
          | exact resolve b2e278163 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e278163
        have b2e278415 : ∀ X0 : G, x = (k (τ (M.op X0 X0)) y) ∨ x = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e278204 (τ X0)
             have i₂ := b2e44732 X0
             grind)
          | exact superpose b2e44732 b2e278204
          | exact resolve b2e278204 b2e44732
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44732 b2e278204
        have b2e279089 : ∀ X0 : G, (σ x) = (k (M.op X0 X0) (σ y)) ∨ x = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e25 (M.op X0 X0) y
             have i₂ := b2e278415 X0
             grind)
          | exact superpose b2e278415 b2e25
          | (have j1 := b2e278415 X0
             grind)
          | exact resolve b2e25 b2e278415
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e278415
        have b2e318785 : ∀ X0 : G, (k (σ (M.op x x)) X0) = (σ (τ (M.op x X0))) ∨ (M.op X0 X0) = (k (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e26 X0 (M.op x x)
             have i₂ := b2e159201 X0
             grind)
          | exact superpose b2e159201 b2e26
          | (have j1 := b2e159201 X0
             grind)
          | exact resolve b2e26 b2e159201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e159201
        have b2e318876 : ∀ X0 : G, (M.op x X0) = (k (σ (M.op x x)) X0) ∨ (M.op X0 X0) = (k (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e318785 X0
             have i₂ := b2e14 (M.op x X0)
             grind)
          | exact superpose b2e14 b2e318785
          | (have j0 := b2e318785 X0
             grind)
          | exact resolve b2e318785 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e318785
        have b2e318917 : ∀ X0 : G, (M.op x X0) = (k (M.op x x) X0) ∨ (M.op X0 X0) = (k (M.op x x) X0) := by
          intro X0
          first
          | (have i₁ := b2e318876 X0
             have i₂ := b2e15529
             grind)
          | exact superpose b2e15529 b2e318876
          | (have j0 := b2e318876 X0
             grind)
          | exact resolve b2e318876 b2e15529
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e318876
        have b2e318980 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op x (σ y)) ∨ x = (τ (M.op x x)) := by
          first
          | (have i₁ := b2e318917 (σ y)
             have i₂ := b2e279089 x
             grind)
          | exact superpose b2e279089 b2e318917
          | (have j1 := b2e279089 x
             grind)
          | exact resolve b2e318917 b2e279089
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e279089 b2e318917
        have b2e319304 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op x (σ y)) ∨ x = (τ (M.op x x)) := by
          first
          | (have i₁ := b2e318980
             have i₂ := b2e44740 y
             grind)
          | exact superpose b2e44740 b2e318980
          | exact resolve b2e318980 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e318980
        have b2e319364 : (σ x) = (M.op x (σ y)) ∨ x = (τ (M.op x x)) := by
          first
          | (have r₁ := b2e319304
             have r₂ := b2e4277
             grind)
          | exact resolve b2e319304 b2e4277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e319304
        have b2e319395 : (σ x) = (M.op x (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e319364
             have i₂ := b2e17534
             grind)
          | exact superpose b2e17534 b2e319364
          | exact resolve b2e319364 b2e17534
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17534 b2e319364
        have b2e319491 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b2e202 x (σ y) X0
             have i₂ := b2e319395
             grind)
          | exact superpose b2e319395 b2e202
          | exact resolve b2e202 b2e319395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e202
        have b2e319854 : (σ x) ≠ (M.op x (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e319491 (σ y)
             grind)
          | exact superpose b2e319491 b2e21
          | exact resolve b2e21 b2e319491
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e319491
        have b2e320760 : x = (M.op x x) := by
          first
          | (have r₁ := b2e319854
             have r₂ := b2e319395
             grind)
          | exact resolve b2e319854 b2e319395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e319395 b2e319854
        have b2e321020 : x = (σ x) := by
          first
          | (have i₁ := b2e15529
             have i₂ := b2e320760
             grind)
          | exact superpose b2e320760 b2e15529
          | exact resolve b2e15529 b2e320760
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15529 b2e320760
        have b2e322414 : x ≠ (M.op x (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e321020
             grind)
          | exact superpose b2e321020 b2e21
          | exact resolve b2e21 b2e321020
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e322416 : (σ (M.op y y)) = (M.op x (σ y)) := by
          first
          | (have i₁ := b2e4276
             have i₂ := b2e321020
             grind)
          | exact superpose b2e321020 b2e4276
          | exact resolve b2e4276 b2e321020
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4276
        have b2e349375 : (M.op y y) = (τ (M.op x (σ y))) := by
          first
          | (have i₁ := b2e13 (M.op y y)
             have i₂ := b2e322416
             grind)
          | exact superpose b2e322416 b2e13
          | exact resolve b2e13 b2e322416
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e352115 : (k (M.op x (σ y)) (σ y)) = (σ (M.op (M.op y y) y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e277440 (M.op x (σ y))
             have i₂ := b2e349375
             grind)
          | exact superpose b2e349375 b2e277440
          | exact resolve b2e277440 b2e349375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277440 b2e349375
        have b2e352120 : (k (M.op x (σ y)) (σ y)) = (σ (M.op y (M.op y y))) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e352115
             have i₂ := b2e12 y y y
             grind)
          | exact superpose b2e12 b2e352115
          | exact resolve b2e352115 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e352115
        have b2e352204 : (σ (M.op x y)) = (k (M.op x (σ y)) (σ y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e352120
             have i₂ := b2e228 y y
             grind)
          | exact superpose b2e228 b2e352120
          | exact resolve b2e352120 b2e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e352120
        have b2e352236 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e352204
             have i₂ := b2e3377 (σ y)
             grind)
          | exact superpose b2e3377 b2e352204
          | exact resolve b2e352204 b2e3377
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3377 b2e352204
        have b2e352251 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e352236
             have i₂ := b2e44740 y
             grind)
          | exact superpose b2e44740 b2e352236
          | exact resolve b2e352236 b2e44740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44740 b2e352236
        have b2e352259 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e352251
             have i₂ := b2e322416
             grind)
          | exact superpose b2e322416 b2e352251
          | exact resolve b2e352251 b2e322416
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e322416 b2e352251
        have b2e352263 : (σ x) = (M.op x (σ y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e352259
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e352259
          | exact resolve b2e352259 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e352259
        have b2e352267 : x = (M.op x (σ y)) ∨ (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have i₁ := b2e352263
             have i₂ := b2e321020
             grind)
          | exact superpose b2e321020 b2e352263
          | exact resolve b2e352263 b2e321020
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e321020 b2e352263
        have b2e352270 : (M.op y y) = (M.op (M.op y y) y) := by
          first
          | (have r₁ := b2e352267
             have r₂ := b2e322414
             grind)
          | exact resolve b2e352267 b2e322414
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e322414 b2e352267
        have b2e352273 : (M.op y y) = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b2e352270
             have i₂ := b2e12 y y y
             grind)
          | exact superpose b2e12 b2e352270
          | exact resolve b2e352270 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e352270
        have b2e352276 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b2e352273
             have i₂ := b2e228 y y
             grind)
          | exact superpose b2e228 b2e352273
          | exact resolve b2e352273 b2e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e228 b2e352273
        have b2e352278 : x = (M.op y y) := by
          first
          | (have i₁ := b2e352276
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e352276
          | exact resolve b2e352276 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e352276
        have b2e352279 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e4277
             have i₂ := b2e352278
             grind)
          | exact superpose b2e352278 b2e4277
          | exact resolve b2e4277 b2e352278
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4277 b2e352278
        have b2e352919 : False := by grind
        exact b2e352919
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e29 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 x X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 X0 X3
             have i₂ := b3e12 X2 X0 X1
             grind)
          | (have i₁ := b3e12 (M.op X1 X2) X1 X2
             have i₂ := b3e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X3 X2 (M.op X0 X0)
             have i₂ := b3e12 X2 X0 X1
             grind)
          | (have i₁ := b3e12 X0 (M.op X1 X2) X0
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op (σ x) X0) := by
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
        have b3e35 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X0 X0) X2 X3
             have i₂ := b3e12 (M.op X2 X3) X0 X1
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e47 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e44
        have b3e48 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e47
          | exact resolve b3e47 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e51 : x = (k x y) ∨ x = (M.op x y) := by grind
        have b3e52 : x = (k x y) := by
          first
          | (have r₁ := b3e51
             have r₂ := b3e20
             grind)
          | exact resolve b3e51 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b3e130 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e15
          | exact resolve b3e15 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e131 : ∀ X0 : G, (M.op X0 (σ (k x y))) = (M.op (σ (k x y)) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y) (σ y)
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e12
          | exact resolve b3e12 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e132 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e131 X0
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e131
          | exact resolve b3e131 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e131
        have b3e133 : (σ x) ≠ (σ y) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e130
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e130
          | exact resolve b3e130 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130
        have b3e138 : (σ (k x y)) = (σ (k y y)) ∨ (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e133
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e133
          | exact resolve b3e133 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e133
        have b3e140 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e138
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e138
          | exact resolve b3e138 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e138
        have b3e164 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e30 X0 X1 X2 y
             have i₂ := b3e35 X0
             grind)
          | (have i₁ := b3e30 y X1 X2 X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e30
          | exact resolve b3e30 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e171 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ (k x y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e30 (σ y) X0 X1 (σ y)
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e30
          | exact resolve b3e30 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e172 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e30 x X0 X1 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e30
          | exact resolve b3e30 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e205 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e171 X0 X1
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e171
          | exact resolve b3e171 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e214 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (M.op y (σ y)) X1) := by
          intro X1
          first
          | (have i₁ := b3e205 x X1
             have i₂ := b3e164 (σ y) x X1
             grind)
          | exact superpose b3e164 b3e205
          | exact resolve b3e205 b3e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e205
        have b3e220 : ∀ X1 : G, (M.op X1 (M.op y y)) = (M.op (σ x) X1) := by
          intro X1
          first
          | (have i₁ := b3e214 X1
             have i₂ := b3e12 X1 y (σ y)
             grind)
          | exact superpose b3e12 b3e214
          | exact resolve b3e214 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e214
        have b3e233 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 (σ x)
             have i₂ := b3e132 X0
             grind)
          | (have i₁ := b3e12 X0 (σ x) X0
             have i₂ := b3e132 X0
             grind)
          | exact superpose b3e132 b3e12
          | exact resolve b3e12 b3e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e241 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op y (σ x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e233 X0 X1
             have i₂ := b3e164 (σ x) X0 X1
             grind)
          | exact superpose b3e164 b3e233
          | exact resolve b3e233 b3e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e233
        have b3e252 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op y y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e241 X0 X1
             have i₂ := b3e12 X1 y (σ x)
             grind)
          | exact superpose b3e12 b3e241
          | exact resolve b3e241 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e241
        have b3e260 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e252 X0 X1
             have i₂ := b3e220 X1
             grind)
          | (have i₁ := b3e252 X0 (σ x)
             have i₂ := b3e220 (M.op y y)
             grind)
          | exact superpose b3e220 b3e252
          | exact resolve b3e252 b3e220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e220 b3e252
        have b3e281 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (σ x) x) X0) := by
          intro X0
          first
          | (have i₁ := b3e29 X0 (M.op (σ x) (σ x))
             have i₂ := b3e34 x
             grind)
          | exact superpose b3e34 b3e29
          | exact resolve b3e29 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34
        have b3e282 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b3e281 X0
             have i₂ := b3e164 (σ x) x X0
             grind)
          | exact superpose b3e164 b3e281
          | exact resolve b3e281 b3e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e281
        have b3e300 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b3e282 X0
             have i₂ := b3e12 X0 y (σ x)
             grind)
          | exact superpose b3e12 b3e282
          | exact resolve b3e282 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e282
        have b3e317 : ∀ X0 : G, (M.op X0 y) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e300 X0
             have i₂ := b3e260 y X0
             grind)
          | exact superpose b3e260 b3e300
          | exact resolve b3e300 b3e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e300
        have b3e371 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e132 X0
             have i₂ := b3e317 X0
             grind)
          | exact superpose b3e317 b3e132
          | exact resolve b3e132 b3e317
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e499 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X4) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e12 (M.op (M.op X2 X3) X1) X0 X4
             have i₂ := b3e32 X2 X3 X1 (M.op X0 X0)
             grind)
          | (have i₁ := b3e12 X3 X2 X2
             have i₂ := b3e32 X0 X1 X2 X3
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e506 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (M.op X0 X4) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e499 X0 X1 X2 X3 X4
             have i₂ := b3e260 X1 (M.op X0 X0)
             grind)
          | exact superpose b3e260 b3e499
          | exact resolve b3e499 b3e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e499
        have b3e566 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) y) = (M.op (M.op X0 X4) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e506 X0 X1 X2 X3 X4
             have i₂ := b3e317 (M.op X0 X0)
             grind)
          | exact superpose b3e317 b3e506
          | exact resolve b3e506 b3e317
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e317 b3e506
        have b3e625 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op X0 X0)) = (M.op (M.op X0 X4) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e566 X0 X1 X2 X3 X4
             have i₂ := b3e12 y X0 X0
             grind)
          | exact superpose b3e12 b3e566
          | exact resolve b3e566 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e566
        have b3e672 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ x) y) = (M.op (M.op X0 X4) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e625 X0 X1 X2 X3 X4
             have i₂ := b3e260 X0 y
             grind)
          | exact superpose b3e260 b3e625
          | exact resolve b3e625 b3e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e260 b3e625
        have b3e710 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (σ x)) = (M.op (M.op X0 X4) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e672 X0 X1 X2 X3 X4
             have i₂ := b3e132 y
             grind)
          | exact superpose b3e132 b3e672
          | exact resolve b3e672 b3e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132 b3e672
        have b3e742 : ∀ X0 X1 X2 X3 X4 : G, (M.op y y) = (M.op (M.op X0 X4) (M.op (M.op X2 X3) X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b3e710 X0 X1 X2 X3 X4
             have i₂ := b3e371 y
             grind)
          | exact superpose b3e371 b3e710
          | exact resolve b3e710 b3e371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e371 b3e710
        have b3e888 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X0 y)) = (M.op (M.op X1 X1) (M.op (M.op x X3) (M.op x X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e36 X1 X2 (M.op x X3) X0
             have i₂ := b3e29 X0 X3
             grind)
          | exact superpose b3e29 b3e36
          | exact resolve b3e36 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e974 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X5) X2) (M.op X0 X0)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b3e32 X4 X5 X2 (M.op X0 X0)
             have i₂ := b3e36 X0 X1 X2 X3
             grind)
          | (have i₁ := b3e32 X0 X1 X3 (M.op X0 X1)
             have i₂ := b3e36 X0 X1 X3 X3
             grind)
          | exact superpose b3e36 b3e32
          | exact resolve b3e32 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e992 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op y (M.op X4 X5)) (M.op X0 X0)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b3e974 X0 X1 X2 X3 X4 X5
             have i₂ := b3e164 (M.op X4 X5) X2 (M.op X0 X0)
             grind)
          | exact superpose b3e164 b3e974
          | exact resolve b3e974 b3e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e164 b3e974
        have b3e1047 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 X2) (M.op X0 y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e888 X0 X1 X2 x
             have i₂ := b3e742 X1 (M.op x x) x x X1
             grind)
          | exact superpose b3e742 b3e888
          | exact resolve b3e888 b3e742
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e742 b3e888
        have b3e1077 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op y y)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e992 X0 X1 X2 X3 x x
             have i₂ := b3e12 (M.op X0 X0) y (M.op x x)
             grind)
          | exact superpose b3e12 b3e992
          | exact resolve b3e992 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e992
        have b3e1138 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op y y) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e1077 X0 X1 X2 X3
             have i₂ := b3e1047 y X0 X0
             grind)
          | exact superpose b3e1047 b3e1077
          | exact resolve b3e1077 b3e1047
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1047 b3e1077
        have b3e2480 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op x x) (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e36 x x X0 X1
             have i₂ := b3e172 x (M.op X0 X1)
             grind)
          | exact superpose b3e172 b3e36
          | exact resolve b3e36 b3e172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36 b3e172
        have b3e2532 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y y) := by
          intro X0 X1
          first
          | (have i₁ := b3e2480 X0 X1
             have i₂ := b3e1138 x x X0 X0
             grind)
          | exact superpose b3e1138 b3e2480
          | exact resolve b3e2480 b3e1138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1138 b3e2480
        have b3e6521 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e58 y y
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e58
          | exact resolve b3e58 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e58
        have b3e6645 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
        clear b3e6521
        have b3e6716 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e6645
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e6645
          | exact resolve b3e6645 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6645
        have b3e6782 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
          first
          | (have i₁ := b3e6716
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e6716
          | exact resolve b3e6716 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e6716
        have b3e6833 : (σ x) = (σ (k y y)) := by
          first
          | (have r₁ := b3e6782
             have r₂ := b3e140
             grind)
          | exact resolve b3e6782 b3e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e140 b3e6782
        have b3e7013 : (k y y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e6833
             grind)
          | exact superpose b3e6833 b3e13
          | exact resolve b3e13 b3e6833
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6833
        have b3e7025 : x = (k y y) := by
          first
          | (have i₁ := b3e7013
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e7013
          | exact resolve b3e7013 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7013
        have b3e7091 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e7025
             grind)
          | exact superpose b3e7025 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e7025
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e7092 : y = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b3e7091
        have b3e18465 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e15 y y
             have i₂ := b3e7092
             grind)
          | exact superpose b3e7092 b3e15
          | (have r₁ := b3e15 y y
             have r₂ := b3e7092
             grind)
          | exact resolve b3e15 b3e7092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e18484 : x ≠ y ∨ x = (M.op y y) := by grind
        clear b3e7092
        have b3e18485 : y = (k y y) ∨ x = (M.op y y) := by grind
        clear b3e18465
        have b3e18488 : x = y ∨ x = (M.op y y) := by
          first
          | (have i₁ := b3e18485
             have i₂ := b3e7025
             grind)
          | exact superpose b3e7025 b3e18485
          | exact resolve b3e18485 b3e7025
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7025 b3e18485
        have b3e18501 : x = (M.op y y) := by
          first
          | (have r₁ := b3e18488
             have r₂ := b3e18484
             grind)
          | exact resolve b3e18488 b3e18484
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e18484 b3e18488
        have b3e20063 : x = (M.op y x) := by
          first
          | (have i₁ := b3e2532 y y
             have i₂ := b3e18501
             grind)
          | exact superpose b3e18501 b3e2532
          | exact resolve b3e2532 b3e18501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2532 b3e18501
        have b3e20065 : x = (M.op x y) := by
          first
          | (have i₁ := b3e20063
             have i₂ := b3e35 x
             grind)
          | exact superpose b3e35 b3e20063
          | exact resolve b3e20063 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e20063
        have b3e20087 : False := by grind
        exact b3e20087
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
          have b4e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b4e26
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X0 X0) X3
               have i₂ := b4e13 (M.op X0 X0) X0 X1
               grind)
            | (have i₁ := b4e13 X0 (M.op X1 X2) X2
               have i₂ := b4e13 (M.op X1 X2) X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 X0 X3
               have i₂ := b4e13 X2 X0 X1
               grind)
            | (have i₁ := b4e13 (M.op X1 X2) X1 X2
               have i₂ := b4e13 (M.op X1 X1) X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 X2 (M.op X0 X0)
               have i₂ := b4e13 X2 X0 X1
               grind)
            | (have i₁ := b4e13 X0 (M.op X1 X2) X0
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 y
               have i₂ := b4e41 X0
               grind)
            | (have i₁ := b4e13 X0 y X0
               have i₂ := b4e41 X0
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (M.op X0 X0) = (k (M.op X1 X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 (M.op X1 X2) X0
               have i₂ := b4e13 X0 X1 X2
               grind)
            | (have i₁ := b4e16 X0 (M.op X1 X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X1 X2) X0
               grind)
            | (have r₁ := b4e16 (M.op X0 (M.op X0 X0)) X0
               have r₂ := b4e13 X0 X0 (M.op X0 X0)
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b4e16 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e53 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b4e50
               have i₂ := b4e19 x x
               grind)
            | exact superpose b4e19 b4e50
            | exact resolve b4e50 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e57 : x = (k x y) ∨ x = (M.op x y) := by grind
          have b4e60 : x = (k x y) := by
            first
            | (have r₁ := b4e57
               have r₂ := b4e21
               grind)
            | exact resolve b4e57 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e68 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X2 ∨ (M.op X1 X2) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 X1 X2
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e18 X0 X1
               have i₂ := b4e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e18 b4e18
            | (have j0 := b4e18 X1 X2
               have j1 := b4e18 X1 X2
               grind)
            | exact resolve b4e18 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b4e75 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 X3) X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3
               have i₂ := b4e18 X2 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X2 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e24
               have i₂ := b4e18 (σ x) X0
               grind)
            | (have i₁ := b4e24
               have i₂ := b4e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b4e18 b4e24
            | (have j1 := b4e18 (σ x) X0
               grind)
            | exact resolve b4e24 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 X1 : G, (M.op (M.op x X0) y) = X1 ∨ (M.op (M.op x X0) X1) = (k (M.op x X0) X1) ∨ (M.op x X0) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e18 (M.op x X0) X1
               have i₂ := b4e35 (M.op x X0) X0
               grind)
            | exact superpose b4e35 b4e18
            | (have j0 := b4e18 (M.op x X0) X1
               grind)
            | exact resolve b4e18 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e97 : ∀ X0 : G, (M.op y y) = (M.op y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e41 (M.op x X0)
               have i₂ := b4e35 y X0
               grind)
            | exact superpose b4e35 b4e41
            | exact resolve b4e41 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e102 : ∀ X0 X1 : G, (M.op y (M.op x x)) = X1 ∨ (M.op (M.op x X0) X1) = (k (M.op x X0) X1) ∨ (M.op x X0) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e91 X0 X1
               have i₂ := b4e13 y x X0
               grind)
            | exact superpose b4e13 b4e91
            | (have j0 := b4e91 X0 X1
               grind)
            | exact resolve b4e91 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e109 : ∀ X0 X1 : G, (M.op y y) = X1 ∨ (M.op (M.op x X0) X1) = (k (M.op x X0) X1) ∨ (M.op x X0) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e102 X0 X1
               have i₂ := b4e97 x
               grind)
            | exact superpose b4e97 b4e102
            | (have j0 := b4e102 X0 X1
               grind)
            | exact resolve b4e102 b4e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97 b4e102
          have b4e113 : ∀ X0 X1 : G, (M.op X1 y) = (k (M.op x X0) X1) ∨ (M.op y y) = X1 ∨ (M.op x X0) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e109 X0 X1
               have i₂ := b4e35 X1 X0
               grind)
            | exact superpose b4e35 b4e109
            | (have j0 := b4e109 X0 X1
               grind)
            | exact resolve b4e109 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e116 : ∀ X0 X1 : G, (M.op X1 y) = (k (M.op x X0) X1) ∨ (M.op X1 y) = (M.op x X0) ∨ (M.op y y) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e113 X0 X1
               have i₂ := b4e35 X1 X0
               grind)
            | exact superpose b4e35 b4e113
            | (have j0 := b4e113 X0 X1
               grind)
            | exact resolve b4e113 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113
          have b4e144 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31
            | exact resolve b4e31 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e156 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op y (σ x)) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0 y
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e34
            | exact resolve b4e34 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e180 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e156 X0
               have i₂ := b4e13 X0 y (σ x)
               grind)
            | exact superpose b4e13 b4e156
            | exact resolve b4e156 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156
          have b4e240 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (σ y) X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e36 X0 X1 X2 (σ y)
               have i₂ := b4e40 X0
               grind)
            | (have i₁ := b4e36 (σ y) X1 X2 X0
               have i₂ := b4e40 X0
               grind)
            | exact superpose b4e40 b4e36
            | exact resolve b4e36 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e241 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e36 X0 X1 X2 y
               have i₂ := b4e41 X0
               grind)
            | (have i₁ := b4e36 y X1 X2 X0
               have i₂ := b4e41 X0
               grind)
            | exact superpose b4e41 b4e36
            | exact resolve b4e36 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e249 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 x X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e294 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y (σ y)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e240 X0 X1 X2
               have i₂ := b4e241 (σ y) X0 X2
               grind)
            | exact superpose b4e241 b4e240
            | exact resolve b4e240 b4e241
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e240
          have b4e307 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op y y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e294 X0 X1 X2
               have i₂ := b4e13 X2 y (σ y)
               grind)
            | exact superpose b4e13 b4e294
            | exact resolve b4e294 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e294
          have b4e316 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (σ y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e307 X0 X1 X2
               have i₂ := b4e180 X2
               grind)
            | exact superpose b4e180 b4e307
            | exact resolve b4e307 b4e180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e307
          have b4e323 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) x) X2) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e249 (M.op X0 X0) X2
               have i₂ := b4e13 x X0 X1
               grind)
            | exact superpose b4e13 b4e249
            | exact resolve b4e249 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e249
          have b4e355 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op y (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e323 X0 X1 X2
               have i₂ := b4e241 (M.op X0 X1) x X2
               grind)
            | exact superpose b4e241 b4e323
            | exact resolve b4e323 b4e241
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e241 b4e323
          have b4e360 : ∀ X2 : G, (M.op X2 (M.op y y)) = (M.op y X2) := by
            intro X2
            first
            | (have i₁ := b4e355 x x X2
               have i₂ := b4e13 X2 y (M.op x x)
               grind)
            | exact superpose b4e13 b4e355
            | exact resolve b4e355 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e355
          have b4e390 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) := by
            intro X0
            first
            | (have i₁ := b4e35 X0 (M.op y y)
               have i₂ := b4e360 x
               grind)
            | exact superpose b4e360 b4e35
            | exact resolve b4e35 b4e360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e360
          have b4e391 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e390 X0
               have i₂ := b4e316 y x X0
               grind)
            | exact superpose b4e316 b4e390
            | exact resolve b4e390 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e390
          have b4e549 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (M.op X2 X3) (M.op X2 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 (M.op X2 X3) X1
               have i₂ := b4e38 X2 X3 X1 X0
               grind)
            | (have i₁ := b4e13 (M.op X2 X2) X1 X2
               have i₂ := b4e38 X0 X1 X2 (M.op X1 X2)
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e572 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y (M.op X2 X3)) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e549 X0 X1 X2 X3
               have i₂ := b4e44 (M.op X2 X3) X0
               grind)
            | exact superpose b4e44 b4e549
            | exact resolve b4e549 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e549
          have b4e633 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op y y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e572 X0 X1 x x
               have i₂ := b4e13 X0 y (M.op x x)
               grind)
            | exact superpose b4e13 b4e572
            | exact resolve b4e572 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e572
          have b4e688 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e633 X0 X1
               have i₂ := b4e180 X0
               grind)
            | exact superpose b4e180 b4e633
            | exact resolve b4e633 b4e180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e180 b4e633
          have b4e735 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e688 X0 X1
               have i₂ := b4e391 X0
               grind)
            | exact superpose b4e391 b4e688
            | exact resolve b4e688 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e688
          have b4e891 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e40 X0
               have i₂ := b4e391 X0
               grind)
            | exact superpose b4e391 b4e40
            | exact resolve b4e40 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e908 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e391 (σ x)
               grind)
            | exact superpose b4e391 b4e20
            | exact resolve b4e20 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e909 : (σ x) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e391 (σ x)
               grind)
            | exact superpose b4e391 b4e23
            | exact resolve b4e23 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e914 : (σ x) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e909
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e909
            | exact resolve b4e909 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e909
          have b4e915 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e908
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e908
            | exact resolve b4e908 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e908
          have b4e1755 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X2 (M.op (M.op X1 X3) (M.op X1 X1))) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e32 X1 X3 X2 (M.op X1 X1)
               have i₂ := b4e18 (M.op X1 X1) X0
               grind)
            | (have i₁ := b4e32 X0 X1 X2 X3
               have i₂ := b4e18 X0 (M.op (M.op X0 X0) X3)
               grind)
            | exact superpose b4e18 b4e32
            | (have j1 := b4e18 (M.op X1 X1) X0
               grind)
            | exact resolve b4e32 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e2011 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op (M.op X1 X1) (σ y))) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e1755 X0 X1 X2 x
               have i₂ := b4e316 X1 x (M.op X1 X1)
               grind)
            | exact superpose b4e316 b4e1755
            | (have j0 := b4e1755 X0 X1 X2 x
               grind)
            | exact resolve b4e1755 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1755
          have b4e2127 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op (σ y) (M.op X1 X1))) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2011 X0 X1 X2
               have i₂ := b4e13 (σ y) X1 X1
               grind)
            | exact superpose b4e13 b4e2011
            | (have j0 := b4e2011 X0 X1 X2
               grind)
            | exact resolve b4e2011 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2011
          have b4e2234 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op (M.op X1 X1) y)) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2127 X0 X1 X2
               have i₂ := b4e891 (M.op X1 X1)
               grind)
            | exact superpose b4e891 b4e2127
            | (have j0 := b4e2127 X0 X1 X2
               grind)
            | exact resolve b4e2127 b4e891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e891 b4e2127
          have b4e2330 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op y (M.op X1 X1))) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2234 X0 X1 X2
               have i₂ := b4e13 y X1 X1
               grind)
            | exact superpose b4e13 b4e2234
            | (have j0 := b4e2234 X0 X1 X2
               grind)
            | exact resolve b4e2234 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2234
          have b4e2421 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X2 (M.op y y)) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2330 X0 X1 X2
               have i₂ := b4e735 y X1
               grind)
            | exact superpose b4e735 b4e2330
            | (have j0 := b4e2330 X0 X1 X2
               grind)
            | exact resolve b4e2330 b4e735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2330
          have b4e2499 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X0 X2) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2421 X0 X1 X2
               have i₂ := b4e735 X2 y
               grind)
            | exact superpose b4e735 b4e2421
            | (have j0 := b4e2421 X0 X1 X2
               grind)
            | exact resolve b4e2421 b4e735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2421
          have b4e2556 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (k (M.op X1 X1) X0) ∨ (M.op X2 y) = (M.op X0 X2) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2499 X0 X1 X2
               have i₂ := b4e316 X1 X1 X0
               grind)
            | exact superpose b4e316 b4e2499
            | (have j0 := b4e2499 X0 X1 X2
               grind)
            | exact resolve b4e2499 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2499
          have b4e2594 : ∀ X0 X1 X2 : G, (M.op X0 y) = (k (M.op X1 X1) X0) ∨ (M.op X2 y) = (M.op X0 X2) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2556 X0 X1 X2
               have i₂ := b4e391 X0
               grind)
            | exact superpose b4e391 b4e2556
            | (have j0 := b4e2556 X0 X1 X2
               grind)
            | exact resolve b4e2556 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2556
          have b4e2621 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (σ y)) ∨ (M.op X0 y) = (k (M.op X1 X1) X0) ∨ (M.op X2 y) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2594 X0 X1 X2
               have i₂ := b4e316 X1 X1 X0
               grind)
            | exact superpose b4e316 b4e2594
            | (have j0 := b4e2594 X0 X1 X2
               grind)
            | exact resolve b4e2594 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2594
          have b4e2638 : ∀ X0 X1 X2 : G, (M.op X0 y) = (k (M.op X1 X1) X0) ∨ (M.op X2 y) = (M.op X0 X2) ∨ (M.op X1 X1) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e2621 X0 X1 X2
               have i₂ := b4e391 X0
               grind)
            | exact superpose b4e391 b4e2621
            | (have j0 := b4e2621 X0 X1 X2
               grind)
            | exact resolve b4e2621 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2621
          have b4e5753 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) X0) := by
            intro X0
            first
            | (have j0 := b4e49 X0 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e5754 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 y) X0) := by
            intro X0
            first
            | (have i₁ := b4e5753 X0
               have i₂ := b4e735 X0 X0
               grind)
            | exact superpose b4e735 b4e5753
            | exact resolve b4e5753 b4e735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5753
          have b4e7951 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e31 (M.op (σ X0) y) X0
               have i₂ := b4e5754 (σ X0)
               grind)
            | exact superpose b4e5754 b4e31
            | exact resolve b4e31 b4e5754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e7954 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op y (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b4e7951 X0
               have i₂ := b4e41 (σ X0)
               grind)
            | exact superpose b4e41 b4e7951
            | exact resolve b4e7951 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7951
          have b4e8301 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = X3 ∨ (M.op X2 X3) = (k X2 X3) ∨ (M.op X2 X3) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e18 X2 X3
               have i₂ := b4e75 X2 X2 X0 X1
               grind)
            | (have i₁ := b4e18 (M.op X2 X3) X1
               have i₂ := b4e75 X0 (M.op X2 X3) X2 X3
               grind)
            | exact superpose b4e75 b4e18
            | (have j0 := b4e18 X2 X3
               have j1 := b4e75 X3 X1 X2 X3
               grind)
            | exact resolve b4e18 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e8438 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e75 X1 X1 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e8441 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e8438 X0 X1 x
               have i₂ := b4e316 X0 x X0
               grind)
            | exact superpose b4e316 b4e8438
            | (have j0 := b4e8438 X0 X1 x
               grind)
            | exact resolve b4e8438 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8438
          have b4e8548 : ∀ X0 X2 X3 : G, (M.op X2 (σ y)) = X3 ∨ (M.op X2 X3) = (k X2 X3) ∨ (M.op X2 X3) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e8301 X0 x X2 X3
               have i₂ := b4e316 X0 x X2
               grind)
            | exact superpose b4e316 b4e8301
            | (have j0 := b4e8301 X0 x X2 X3
               grind)
            | exact resolve b4e8301 b4e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e316 b4e8301
          have b4e8629 : ∀ X0 X1 : G, (M.op X0 y) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e8441 X0 X1
               have i₂ := b4e391 X0
               grind)
            | exact superpose b4e391 b4e8441
            | (have j0 := b4e8441 X0 X1
               grind)
            | exact resolve b4e8441 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8441
          have b4e8726 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X3) = X2 ∨ (M.op X2 y) = X3 ∨ (M.op X0 X2) = X0 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e8548 X0 X2 X3
               have i₂ := b4e391 X2
               grind)
            | exact superpose b4e391 b4e8548
            | (have j0 := b4e8548 X0 X2 X3
               grind)
            | exact resolve b4e8548 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8548
          have b4e9256 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e71 x x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e71
            | exact resolve b4e71 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e9384 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b4e9256
          have b4e9452 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b4e9384
               have r₂ := b4e53
               grind)
            | exact resolve b4e9384 b4e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53 b4e9384
          have b4e9735 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b4e14 (k x x)
               have i₂ := b4e9452
               grind)
            | exact superpose b4e9452 b4e14
            | exact resolve b4e14 b4e9452
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9736 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 (k x x) X0
               have i₂ := b4e9452
               grind)
            | exact superpose b4e9452 b4e19
            | exact resolve b4e19 b4e9452
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9737 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 (k x x)
               have i₂ := b4e9452
               grind)
            | exact superpose b4e9452 b4e19
            | exact resolve b4e19 b4e9452
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9452
          have b4e9749 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k x x))) := by
            intro X0
            first
            | (have i₁ := b4e9737 X0
               have i₂ := b4e19 X0 y
               grind)
            | exact superpose b4e19 b4e9737
            | exact resolve b4e9737 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9737
          have b4e9750 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) := by
            intro X0
            first
            | (have i₁ := b4e9736 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e9736
            | exact resolve b4e9736 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9736
          have b4e9751 : y = (k x x) := by
            first
            | (have i₁ := b4e9735
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e9735
            | exact resolve b4e9735 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9735
          have b4e9798 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x X0) = (k x X0) ∨ y = X0 ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e60
               have i₂ := b4e68 y x X0
               grind)
            | exact superpose b4e68 b4e60
            | (have j1 := b4e68 X0 x X0
               grind)
            | exact resolve b4e60 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e9804 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x X0) = (k x X0) ∨ y = X0 ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e9798 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9798
          have b4e9812 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b4e9804 X0
               have j1 := b4e8629 x X0
               grind)
            | (have r₁ := b4e9804 X0
               have r₂ := b4e8629 x x
               grind)
            | (have r₁ := b4e9804 (M.op y y)
               have r₂ := b4e8629 y x
               grind)
            | (have r₁ := b4e9804 y
               have r₂ := b4e8629 x x
               grind)
            | exact resolve b4e9804 b4e8629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9804
          have b4e31792 : (σ (k (σ x) y)) = (σ (M.op (σ x) (k x x))) ∨ (σ y) = (k x x) ∨ (σ x) = (M.op (σ x) (k x x)) := by
            first
            | (have i₁ := b4e9749 (σ x)
               have i₂ := b4e80 (k x x)
               grind)
            | exact superpose b4e80 b4e9749
            | (have j1 := b4e80 (k x x)
               grind)
            | exact resolve b4e9749 b4e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80 b4e9749
          have b4e31818 : (σ (k (σ x) y)) = (σ (M.op (σ x) y)) ∨ (σ y) = (k x x) ∨ (σ x) = (M.op (σ x) (k x x)) := by
            first
            | (have i₁ := b4e31792
               have i₂ := b4e9751
               grind)
            | exact superpose b4e9751 b4e31792
            | exact resolve b4e31792 b4e9751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31792
          have b4e31830 : (σ (k (σ x) y)) = (σ (M.op y (σ x))) ∨ (σ y) = (k x x) ∨ (σ x) = (M.op (σ x) (k x x)) := by
            first
            | (have i₁ := b4e31818
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e31818
            | exact resolve b4e31818 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31818
          have b4e31840 : y = (σ y) ∨ (σ (k (σ x) y)) = (σ (M.op y (σ x))) ∨ (σ x) = (M.op (σ x) (k x x)) := by
            first
            | (have i₁ := b4e31830
               have i₂ := b4e9751
               grind)
            | exact superpose b4e9751 b4e31830
            | exact resolve b4e31830 b4e9751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31830
          have b4e31847 : (σ x) = (M.op (σ x) y) ∨ y = (σ y) ∨ (σ (k (σ x) y)) = (σ (M.op y (σ x))) := by
            first
            | (have i₁ := b4e31840
               have i₂ := b4e9751
               grind)
            | exact superpose b4e9751 b4e31840
            | exact resolve b4e31840 b4e9751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31840
          have b4e31852 : (σ x) = (M.op y (σ x)) ∨ y = (σ y) ∨ (σ (k (σ x) y)) = (σ (M.op y (σ x))) := by
            first
            | (have i₁ := b4e31847
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e31847
            | exact resolve b4e31847 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31847
          have b4e31855 : (σ (k (σ x) y)) = (σ (M.op y (σ x))) ∨ y = (σ y) := by
            first
            | (have r₁ := b4e31852
               have r₂ := b4e914
               grind)
            | exact resolve b4e31852 b4e914
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e914 b4e31852
          have b4e51563 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = y ∨ x = (M.op x (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e27 X0 x
               have i₂ := b4e9812 (τ X0)
               grind)
            | exact superpose b4e9812 b4e27
            | (have j1 := b4e9812 (τ X0)
               grind)
            | exact resolve b4e27 b4e9812
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e9812
          have b4e65724 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 y) ∨ (M.op y y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e116 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e116
            | (have j0 := b4e116 X0 X0
               grind)
            | exact resolve b4e116 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e78728 : ∀ X0 X1 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X1) = (M.op X1 y) ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e2638 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2638
            | (have j0 := b4e2638 X0 X1 X1
               grind)
            | exact resolve b4e2638 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2638
          have b4e106567 : (k (σ x) y) = (τ (σ (M.op y (σ x)))) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e14 (k (σ x) y)
               have i₂ := b4e31855
               grind)
            | exact superpose b4e31855 b4e14
            | exact resolve b4e14 b4e31855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31855
          have b4e106619 : (M.op y (σ x)) = (k (σ x) y) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e106567
               have i₂ := b4e14 (M.op y (σ x))
               grind)
            | exact superpose b4e14 b4e106567
            | exact resolve b4e106567 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e106567
          have b4e129402 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 x) = (k X0 x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e60
               have i₂ := b4e8726 X0 x y
               grind)
            | exact superpose b4e8726 b4e60
            | (have j1 := b4e8726 X0 x y
               grind)
            | exact resolve b4e60 b4e8726
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e129514 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e8726 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8726
          have b4e129515 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b4e129514 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129514
          have b4e129516 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b4e129515 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129515
          have b4e129554 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 x) = (k X0 x) ∨ y = (M.op x y) ∨ (M.op X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b4e129402 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129402
          have b4e129646 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b4e129516 X0
               have j1 := b4e8629 X0 X0
               grind)
            | (have r₁ := b4e129516 y
               have r₂ := b4e8629 y x
               grind)
            | (have r₁ := b4e129516 X0
               have r₂ := b4e8629 X0 x
               grind)
            | exact resolve b4e129516 b4e8629
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8629 b4e129516
          have b4e129711 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (M.op x y) ∨ (M.op X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b4e129554 X0
               grind)
            | (have r₁ := b4e129554 X0
               have r₂ := b4e21
               grind)
            | exact resolve b4e129554 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129554
          have b4e129841 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e129646 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e129646 x
               have r₂ := b4e16 x x
               grind)
            | exact resolve b4e129646 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129646
          have b4e130567 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e144 X0 X0
               have i₂ := b4e129841 (τ X0)
               grind)
            | exact superpose b4e129841 b4e144
            | exact resolve b4e144 b4e129841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144
          have b4e130591 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e130567 X0
               have i₂ := b4e129841 X0
               grind)
            | exact superpose b4e129841 b4e130567
            | exact resolve b4e130567 b4e129841
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129841 b4e130567
          have b4e131998 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e735 X1 (τ X0)
               have i₂ := b4e130591 X0
               grind)
            | exact superpose b4e130591 b4e735
            | exact resolve b4e735 b4e130591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e735 b4e130591
          have b4e139735 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
            intro X0
            first
            | (have i₁ := b4e131998 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e131998
            | exact resolve b4e131998 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131998
          have b4e300046 : (σ (k y x)) = (σ (M.op (k x x) x)) ∨ y = (M.op x y) ∨ (k x x) = (M.op (k x x) x) := by
            first
            | (have i₁ := b4e9750 x
               have i₂ := b4e129711 (k x x)
               grind)
            | exact superpose b4e129711 b4e9750
            | (have j1 := b4e129711 (k x x)
               grind)
            | exact resolve b4e9750 b4e129711
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9750 b4e129711
          have b4e300062 : (σ (k y x)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ (k x x) = (M.op (k x x) x) := by
            first
            | (have i₁ := b4e300046
               have i₂ := b4e9751
               grind)
            | exact superpose b4e9751 b4e300046
            | exact resolve b4e300046 b4e9751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300046
          have b4e300074 : (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (k x x) = (M.op (k x x) x) := by
            first
            | (have i₁ := b4e300062
               have i₂ := b4e41 x
               grind)
            | exact superpose b4e41 b4e300062
            | exact resolve b4e300062 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300062
          have b4e300084 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e300074
               have i₂ := b4e9751
               grind)
            | exact superpose b4e9751 b4e300074
            | exact resolve b4e300074 b4e9751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9751 b4e300074
          have b4e300093 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e300084
               have i₂ := b4e41 x
               grind)
            | exact superpose b4e41 b4e300084
            | exact resolve b4e300084 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300084
          have b4e300094 : (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
          clear b4e300093
          have b4e300113 : (k y x) = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e300094
               grind)
            | exact superpose b4e300094 b4e14
            | exact resolve b4e14 b4e300094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e300156 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e300113
               have i₂ := b4e14 (M.op x y)
               grind)
            | exact superpose b4e14 b4e300113
            | exact resolve b4e300113 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300113
          have b4e314185 : (σ x) ≠ (M.op (σ y) y) ∨ (M.op (σ x) y) = (k y (σ x)) ∨ y = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e78728 (σ x) (σ y)
               grind)
            | exact superpose b4e78728 b4e23
            | (have j1 := b4e78728 (σ x) x
               grind)
            | exact resolve b4e23 b4e78728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78728
          have b4e314519 : (σ x) ≠ (M.op y (σ y)) ∨ (M.op (σ x) y) = (k y (σ x)) ∨ y = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e314185
               have i₂ := b4e40 y
               grind)
            | exact superpose b4e40 b4e314185
            | exact resolve b4e314185 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e314185
          have b4e314800 : (σ x) ≠ (M.op y y) ∨ (M.op (σ x) y) = (k y (σ x)) ∨ y = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e314519
               have i₂ := b4e391 y
               grind)
            | exact superpose b4e391 b4e314519
            | exact resolve b4e314519 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e391 b4e314519
          have b4e314980 : (M.op (σ x) y) = (k y (σ x)) ∨ y = (M.op (σ x) y) := by
            first
            | (have j1 := b4e65724 (σ x)
               grind)
            | (have r₁ := b4e314800
               have r₂ := b4e65724 (σ x)
               grind)
            | exact resolve b4e314800 b4e65724
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65724 b4e314800
          have b4e315083 : (M.op y (σ x)) = (k y (σ x)) ∨ y = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e314980
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e314980
            | exact resolve b4e314980 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e314980
          have b4e315146 : (M.op y (σ x)) = (k y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e315083
               have i₂ := b4e41 (σ x)
               grind)
            | exact superpose b4e41 b4e315083
            | exact resolve b4e315083 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e315083
          have b4e321532 : (σ (M.op x y)) = (k (σ x) y) ∨ y = (τ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e51563 y
               have i₂ := b4e139735 x
               grind)
            | exact superpose b4e139735 b4e51563
            | (have j0 := b4e51563 y
               grind)
            | exact resolve b4e51563 b4e139735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51563 b4e139735
          have b4e321546 : (σ (M.op x y)) = (k (σ x) y) ∨ y = (τ y) := by
            first
            | (have r₁ := b4e321532
               have r₂ := b4e21
               grind)
            | exact resolve b4e321532 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e321532
          have b4e321643 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (σ y) ∨ y = (τ y) := by
            first
            | (have i₁ := b4e106619
               have i₂ := b4e321546
               grind)
            | exact superpose b4e321546 b4e106619
            | exact resolve b4e106619 b4e321546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e106619 b4e321546
          have b4e321669 : y = (τ y) ∨ y = (σ y) := by
            first
            | (have r₁ := b4e321643
               have r₂ := b4e915
               grind)
            | exact resolve b4e321643 b4e915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e321643
          have b4e322044 : y = (σ y) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e15 y
               have i₂ := b4e321669
               grind)
            | exact superpose b4e321669 b4e15
            | exact resolve b4e15 b4e321669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e321669
          have b4e322092 : y = (σ y) := by grind
          clear b4e322044
          have b4e322232 : y = (τ y) := by
            first
            | (have i₁ := b4e14 y
               have i₂ := b4e322092
               grind)
            | exact superpose b4e322092 b4e14
            | exact resolve b4e14 b4e322092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e322233 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e322092
               grind)
            | exact superpose b4e322092 b4e19
            | exact resolve b4e19 b4e322092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e322909 : (M.op y (σ x)) = (σ (k y x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e315146
               have i₂ := b4e322233 x
               grind)
            | exact superpose b4e322233 b4e315146
            | exact resolve b4e315146 b4e322233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e315146 b4e322233
          have b4e334362 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e300094
               have i₂ := b4e322909
               grind)
            | exact superpose b4e322909 b4e300094
            | exact resolve b4e300094 b4e322909
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300094
          have b4e334397 : y = (M.op y (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e334362
               have r₂ := b4e915
               grind)
            | exact resolve b4e334362 b4e915
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e334362
          have b4e334580 : (τ (M.op (σ x) (σ x))) = (k (τ y) x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e7954 x
               have i₂ := b4e334397
               grind)
            | exact superpose b4e334397 b4e7954
            | exact resolve b4e7954 b4e334397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7954 b4e334397
          have b4e334703 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e334580
               have i₂ := b4e322232
               grind)
            | exact superpose b4e322232 b4e334580
            | exact resolve b4e334580 b4e322232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e322232 b4e334580
          have b4e334725 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e334703
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e334703
            | exact resolve b4e334703 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e334703
          have b4e334739 : y = (k y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e334725
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e334725
            | exact resolve b4e334725 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e334725
          have b4e335348 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e300156
               have i₂ := b4e334739
               grind)
            | exact superpose b4e334739 b4e300156
            | exact resolve b4e300156 b4e334739
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300156 b4e334739
          have b4e335384 : y = (M.op x y) := by grind
          clear b4e335348
          have b4e335563 : (σ y) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e915
               have i₂ := b4e335384
               grind)
            | exact superpose b4e335384 b4e915
            | exact resolve b4e915 b4e335384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e915
          have b4e335589 : (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e5754 x
               have i₂ := b4e335384
               grind)
            | exact superpose b4e335384 b4e5754
            | exact resolve b4e5754 b4e335384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5754 b4e335384
          have b4e335725 : y = (k y x) := by
            first
            | (have i₁ := b4e335589
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e335589
            | exact resolve b4e335589 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335589
          have b4e335736 : y ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e335563
               have i₂ := b4e322092
               grind)
            | exact superpose b4e322092 b4e335563
            | exact resolve b4e335563 b4e322092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335563
          have b4e335988 : (σ y) = (M.op y (σ x)) ∨ y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e322909
               have i₂ := b4e335725
               grind)
            | exact superpose b4e335725 b4e322909
            | exact resolve b4e322909 b4e335725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e322909 b4e335725
          have b4e336074 : (σ y) = (M.op y (σ x)) := by
            first
            | (have r₁ := b4e335988
               have r₂ := b4e335736
               grind)
            | exact resolve b4e335988 b4e335736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e335988
          have b4e336091 : y = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e336074
               have i₂ := b4e322092
               grind)
            | exact superpose b4e322092 b4e336074
            | exact resolve b4e336074 b4e322092
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e322092 b4e336074
          have b4e336097 : False := by grind
          exact b4e336097
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e52 : x = (k x y) ∨ x = (M.op x y) := by grind
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e21
               grind)
            | exact resolve b5e52 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e72 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4142 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e72 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e4143 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e4142
               have r₂ := b5e23
               grind)
            | exact resolve b5e4142 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4142
          have b5e4144 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e4143
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e4143
            | exact resolve b5e4143 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4143
          have b5e4145 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e4144
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e4144
            | exact resolve b5e4144 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e4144
          have b5e4146 : False := by grind
          exact b5e4146
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
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
        have b6e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 X0 X3
             have i₂ := b6e12 X2 X0 X1
             grind)
          | (have i₁ := b6e12 (M.op X1 X2) X1 X2
             have i₂ := b6e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op (σ x) X0) := by
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
        have b6e38 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e25 X0 X1
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e39 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X1 X2) ∨ (M.op X0 X0) = (k (M.op X1 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 (M.op X1 X2) X0
             have i₂ := b6e12 X0 X1 X2
             grind)
          | (have i₁ := b6e15 X0 (M.op X1 X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X1 X2) X0
             grind)
          | (have r₁ := b6e15 (M.op X0 (M.op X0 X0)) X0
             have r₂ := b6e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e39
        have b6e43 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e42
          | exact resolve b6e42 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e58 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e43
             grind)
          | exact superpose b6e43 b6e15
          | exact resolve b6e15 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : (σ y) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b6e70 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e71 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 X3) X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X2 X3
             have i₂ := b6e17 X2 X0
             grind)
          | (have i₁ := b6e12 X0 X1 X2
             have i₂ := b6e17 X0 (M.op X1 X1)
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 X2 X0
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b6e17 b6e15
          | (have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e15 (M.op X0 X0) X1
             have r₂ := b6e17 X0 (M.op (M.op X0 X0) X1)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e77 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e70 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e99 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ x) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 (σ x) X0 X1 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e29
          | exact resolve b6e29 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e151 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e29 X0 (M.op (σ x) (σ x)) X1 X2
             have i₂ := b6e31 X0
             grind)
          | exact superpose b6e31 b6e29
          | exact resolve b6e29 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e153 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op (σ x) (σ x))
             have i₂ := b6e31 X0
             grind)
          | exact superpose b6e31 b6e12
          | exact resolve b6e12 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e160 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e153 X0 X1
             have i₂ := b6e99 X0 X1
             grind)
          | exact superpose b6e99 b6e153
          | exact resolve b6e153 b6e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e162 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e151 X0 X1 X2
             have i₂ := b6e99 X0 X1
             grind)
          | exact superpose b6e99 b6e151
          | exact resolve b6e151 b6e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99 b6e151
        have b6e183 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (σ x) X1) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e160 X2 X1
             have i₂ := b6e17 X2 X0
             grind)
          | (have i₁ := b6e160 X0 X1
             have i₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e17 b6e160
          | (have j1 := b6e17 X2 X0
             grind)
          | exact resolve b6e160 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e420 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (k x y)) X0) := by
          intro X0
          first
          | (have i₁ := b6e162 (σ y) X0 (σ y)
             have i₂ := b6e43
             grind)
          | exact superpose b6e43 b6e162
          | exact resolve b6e162 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2433 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b6e420 X0
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e420
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e420 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2504 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
          intro X0
          first
          | (have j0 := b6e2433 X0
             grind)
          | (have r₁ := b6e2433 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e2433 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2433
        have b6e2528 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) := by
          intro X0
          first
          | (have j0 := b6e2504 X0
             grind)
          | (have r₁ := b6e2504 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e2504 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2504
        have b6e2746 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) X0) := by
          intro X0
          first
          | (have j0 := b6e41 X0 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e2747 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e2746 X0
             have i₂ := b6e160 X0 X0
             grind)
          | exact superpose b6e160 b6e2746
          | exact resolve b6e2746 b6e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2746
        have b6e3593 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e73 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e3594 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e3593 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e3593 x
             have r₂ := b6e15 x x
             grind)
          | exact resolve b6e3593 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3593
        have b6e3603 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e3594 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3702 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = X3 ∨ (M.op X2 X3) = (k X2 X3) ∨ (M.op X2 X3) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e17 X2 X3
             have i₂ := b6e71 X2 X2 X0 X1
             grind)
          | (have i₁ := b6e17 (M.op X2 X3) X1
             have i₂ := b6e71 X0 (M.op X2 X3) X2 X3
             grind)
          | exact superpose b6e71 b6e17
          | (have j0 := b6e17 X2 X3
             have j1 := b6e71 X3 X1 X2 X3
             grind)
          | exact resolve b6e17 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3826 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b6e71 X1 X1 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e3829 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e3826 X0 X1 x
             have i₂ := b6e162 X0 X0 x
             grind)
          | exact superpose b6e162 b6e3826
          | (have j0 := b6e3826 X0 X1 x
             grind)
          | exact resolve b6e3826 b6e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3826
        have b6e3924 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op (σ x) X2) = X3 ∨ (M.op X2 X3) = X2 ∨ (M.op X0 X2) = X0 := by
          intro X0 X2 X3
          first
          | (have i₁ := b6e3702 X0 x X2 X3
             have i₂ := b6e162 X0 X2 x
             grind)
          | exact superpose b6e162 b6e3702
          | (have j0 := b6e3702 X0 x X2 X3
             grind)
          | exact resolve b6e3702 b6e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3702
        have b6e4138 : (σ y) ≠ (σ (k x y)) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e3603 (σ y)
             have i₂ := b6e43
             grind)
          | exact superpose b6e43 b6e3603
          | (have j0 := b6e3603 (σ y)
             grind)
          | exact resolve b6e3603 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3603
        have b6e4187 : (σ y) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e4138
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e4138
          | exact resolve b6e4138 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4138
        have b6e4214 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e67 y y
             have i₂ := b6e43
             grind)
          | exact superpose b6e43 b6e67
          | exact resolve b6e67 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e4345 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
        clear b6e4214
        have b6e4411 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have r₁ := b6e4345
             have r₂ := b6e60
             grind)
          | exact resolve b6e4345 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e4345
        have b6e4477 : (k y y) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e4411
             grind)
          | exact superpose b6e4411 b6e13
          | exact resolve b6e13 b6e4411
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4493 : (k x y) = (k y y) := by
          first
          | (have i₁ := b6e4477
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e4477
          | exact resolve b6e4477 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4477
        have b6e4548 : (k x y) = (M.op y y) ∨ y = (k x y) := by
          first
          | (have i₁ := b6e3594 y
             have i₂ := b6e4493
             grind)
          | exact superpose b6e4493 b6e3594
          | exact resolve b6e3594 b6e4493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3594 b6e4493
        have b6e5478 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (k x y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e4548
             grind)
          | exact superpose b6e4548 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e4548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4548
        have b6e5480 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (k x y) := by
          first
          | (have r₁ := b6e5478
             have r₂ := b6e21
             grind)
          | exact resolve b6e5478 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5478
        have b6e5490 : y = (k x y) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e5480
             have r₂ := b6e20
             grind)
          | exact resolve b6e5480 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5480
        have b6e7321 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b6e420 X0
             have i₂ := b6e5490
             grind)
          | exact superpose b6e5490 b6e420
          | exact resolve b6e420 b6e5490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e420
        have b6e15704 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e4187
             have i₂ := b6e5490
             grind)
          | exact superpose b6e5490 b6e4187
          | exact resolve b6e4187 b6e5490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4187 b6e5490
        have b6e15714 : (σ y) = (σ (k y y)) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e15704
        have b6e15724 : (σ y) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e15714
             have i₂ := b6e4411
             grind)
          | exact superpose b6e4411 b6e15714
          | exact resolve b6e15714 b6e4411
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15714
        have b6e19436 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e15724
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e15724
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e15724 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e19487 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have r₁ := b6e19436
             have r₂ := b6e21
             grind)
          | exact resolve b6e19436 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e19436
        have b6e19492 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e19487
             have r₂ := b6e20
             grind)
          | exact resolve b6e19487 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e19487
        have b6e22413 : (σ x) ≠ (σ y) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e19492
             grind)
          | exact superpose b6e19492 b6e24
          | exact resolve b6e24 b6e19492
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e19492
        have b6e44555 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e7321 (σ y)
             grind)
          | exact superpose b6e7321 b6e43
          | exact resolve b6e43 b6e7321
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7321
        have b6e44750 : (σ x) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e44555
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e44555
          | exact resolve b6e44555 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44555
        have b6e46326 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e15724
             have i₂ := b6e44750
             grind)
          | exact superpose b6e44750 b6e15724
          | exact resolve b6e15724 b6e44750
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15724 b6e44750
        have b6e46370 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e46326
        have b6e46392 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e46370
             have r₂ := b6e22413
             grind)
          | exact resolve b6e46370 b6e22413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e22413 b6e46370
        have b6e47380 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e3924 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3924
        have b6e47382 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e47380 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47380
        have b6e47383 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e47382 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47382
        have b6e47443 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e47383 X0
             have j1 := b6e3829 X0 X0
             grind)
          | (have r₁ := b6e47383 X0
             have r₂ := b6e3829 X0 x
             grind)
          | (have r₁ := b6e47383 (σ x)
             have r₂ := b6e3829 (σ x) x
             grind)
          | exact resolve b6e47383 b6e3829
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3829 b6e47383
        have b6e47601 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e47443 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e47443 x
             have r₂ := b6e15 x x
             grind)
          | exact resolve b6e47443 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47443
        have b6e48008 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e4411
             have i₂ := b6e47601 y
             grind)
          | exact superpose b6e47601 b6e4411
          | exact resolve b6e4411 b6e47601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4411 b6e47601
        have b6e48011 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e48008
             have i₂ := b6e46392
             grind)
          | exact superpose b6e46392 b6e48008
          | exact resolve b6e48008 b6e46392
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48008
        have b6e191332 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e43
             have i₂ := b6e183 (σ y) (σ y) X0
             grind)
          | exact superpose b6e183 b6e43
          | (have j1 := b6e183 (σ y) x X0
             grind)
          | exact resolve b6e43 b6e183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e183
        have b6e191777 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e191332 X0
             have i₂ := b6e48011
             grind)
          | exact superpose b6e48011 b6e191332
          | (have j0 := b6e191332 X0
             grind)
          | exact resolve b6e191332 b6e48011
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48011 b6e191332
        have b6e192038 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e191777 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e191777
          | (have j0 := b6e191777 X0
             grind)
          | exact resolve b6e191777 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e191777
        have b6e192147 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e192038 X0
             grind)
          | (have r₁ := b6e192038 X0
             have r₂ := b6e24
             grind)
          | exact resolve b6e192038 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e192038
        have b6e192222 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e38 X0 y
             have i₂ := b6e192147 X0
             grind)
          | exact superpose b6e192147 b6e38
          | (have j1 := b6e192147 X0
             grind)
          | exact resolve b6e38 b6e192147
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e192147
        have b6e204185 : (τ (M.op (σ x) (σ y))) = (k (τ (σ (M.op x y))) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e192222 (σ (M.op x y))
             have i₂ := b6e2528 (σ y)
             grind)
          | exact superpose b6e2528 b6e192222
          | exact resolve b6e192222 b6e2528
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2528 b6e192222
        have b6e204321 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e204185
             have i₂ := b6e13 (M.op x y)
             grind)
          | exact superpose b6e13 b6e204185
          | exact resolve b6e204185 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204185
        have b6e204383 : (τ (σ x)) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e204321
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e204321
          | exact resolve b6e204321 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204321
        have b6e204441 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e204383
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e204383
          | exact resolve b6e204383 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204383
        have b6e204474 : (σ (M.op x y)) = (σ x) ∨ x = (k (M.op x y) y) := by
          first
          | (have i₁ := b6e204441
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e204441
          | exact resolve b6e204441 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204441
        have b6e204494 : x = (k (M.op x y) y) := by
          first
          | (have r₁ := b6e204474
             have r₂ := b6e24
             grind)
          | exact resolve b6e204474 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e204474
        have b6e204575 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e77 y (M.op x y)
             have i₂ := b6e204494
             grind)
          | exact superpose b6e204494 b6e77
          | (have j0 := b6e77 y (M.op x y)
             grind)
          | exact resolve b6e77 b6e204494
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e204591 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
          first
          | (have r₁ := b6e204575
             have r₂ := b6e20
             grind)
          | exact resolve b6e204575 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204575
        have b6e204609 : x = (M.op y (M.op x x)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
          first
          | (have i₁ := b6e204591
             have i₂ := b6e12 y x y
             grind)
          | exact superpose b6e12 b6e204591
          | exact resolve b6e204591 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204591
        have b6e204625 : x = (M.op (σ x) y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
          first
          | (have i₁ := b6e204609
             have i₂ := b6e160 x y
             grind)
          | exact superpose b6e160 b6e204609
          | exact resolve b6e204609 b6e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204609
        have b6e204639 : (M.op x y) = (M.op y (M.op x x)) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e204625
             have i₂ := b6e12 y x y
             grind)
          | exact superpose b6e12 b6e204625
          | exact resolve b6e204625 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204625
        have b6e204649 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e204639
             have i₂ := b6e160 x y
             grind)
          | exact superpose b6e160 b6e204639
          | exact resolve b6e204639 b6e160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e160 b6e204639
        have b6e205844 : (M.op y y) = (k (M.op x y) y) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e2747 y
             have i₂ := b6e204649
             grind)
          | exact superpose b6e204649 b6e2747
          | exact resolve b6e2747 b6e204649
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2747 b6e204649
        have b6e205915 : x = (M.op y y) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e205844
             have i₂ := b6e204494
             grind)
          | exact superpose b6e204494 b6e205844
          | exact resolve b6e205844 b6e204494
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204494 b6e205844
        have b6e205931 : x = (M.op x y) ∨ x = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e205915
             have i₂ := b6e46392
             grind)
          | exact superpose b6e46392 b6e205915
          | exact resolve b6e205915 b6e46392
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46392 b6e205915
        have b6e205939 : x = (M.op (σ x) y) := by
          first
          | (have r₁ := b6e205931
             have r₂ := b6e20
             grind)
          | exact resolve b6e205931 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e205931
        have b6e206027 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e162 (σ x) X0 y
             have i₂ := b6e205939
             grind)
          | exact superpose b6e205939 b6e162
          | exact resolve b6e162 b6e205939
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e162
        have b6e206558 : x = (M.op x y) := by
          first
          | (have i₁ := b6e205939
             have i₂ := b6e206027 y
             grind)
          | exact superpose b6e206027 b6e205939
          | exact resolve b6e205939 b6e206027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e205939 b6e206027
        have b6e206895 : False := by grind
        exact b6e206895
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e59 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          have b7e64 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e23
               grind)
            | exact resolve b7e59 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e65 : (σ x) = (σ (k x y)) := by
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
          have b7e68 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e65
               grind)
            | exact superpose b7e65 b7e14
            | exact resolve b7e14 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : x = (k x y) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e68
            | exact resolve b7e68 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e92 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e93 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e92
          have b7e95 : y = (M.op x x) := by
            first
            | (have r₁ := b7e93
               have r₂ := b7e21
               grind)
            | exact resolve b7e93 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e97 : False := by grind
          exact b7e97
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e90 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b8e2171 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e90 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e2172 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e2171
               have r₂ := b8e23
               grind)
            | exact resolve b8e2171 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2171
          have b8e2173 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e2172
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e2172
            | exact resolve b8e2172 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2172
          have b8e2174 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2173
               grind)
            | exact superpose b8e2173 b8e20
            | exact resolve b8e20 b8e2173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2173
          have b8e2714 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e2174
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2174
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e2174 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2174
          have b8e2715 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e2714
          have b8e2720 : x = (M.op x y) := by
            first
            | (have r₁ := b8e2715
               have r₂ := b8e22
               grind)
            | exact resolve b8e2715 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2715
          have b8e2725 : False := by grind
          exact b8e2725

/-- `Equation4535`: `x ◇ (y ◇ z) = (y ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation4535 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4535 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4535.models_iff G M).mp hM
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
    · rcases eq_or_ne (y) (x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          grind
        have b0e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          grind
        clear b0e30
        have b0e68 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
        clear b0e31
        have b0e71 : False := by grind
        exact b0e71
      · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
        · have b1e21 : x = y := by grind
          have b1e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e30 : False := by grind
          exact b1e30
        · have b2e21 : x = y := by grind
          have b2e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : False := by grind
          exact b2e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b3e21 : x = y := by grind
          have b3e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e30 : False := by grind
          exact b3e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b4e22 : x = y := by grind
            have b4e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e33 : False := by grind
            exact b4e33
          · have b5e22 : x = y := by grind
            have b5e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e33 : False := by grind
            exact b5e33
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b6e21 : x = y := by grind
          have b6e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e30 : False := by grind
          exact b6e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b7e22 : x = y := by grind
            have b7e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e33 : False := by grind
            exact b7e33
          · have b8e22 : x = y := by grind
            have b8e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e33 : False := by grind
            exact b8e33
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b9e21 : x ≠ y := by grind
          have b9e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e30 : False := by grind
          exact b9e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e24 : (σ x) = (σ y) := by grind
            have b10e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 y
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e15
              | exact resolve b10e15 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : x = y := by
              first
              | (have i₁ := b10e30
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e30
              | exact resolve b10e30 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e30
            have b10e32 : False := by grind
            exact b10e32
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e24 : (σ x) = (σ y) := by grind
            have b11e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e29 : y = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 y
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e15
              | exact resolve b11e15 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e30 : x = y := by
              first
              | (have i₁ := b11e29
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e29
              | exact resolve b11e29 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e31 : False := by grind
            exact b11e31
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b12e24 : (σ x) ≠ (σ y) := by grind
            have b12e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e33 : False := by grind
            exact b12e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b13e24 : y = (M.op y x) := by grind
              have b13e27 : x ≠ y := by grind
              have b13e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e47 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X0 x y X1
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e58 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b13e47 X0 y
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e47
                | exact resolve b13e47 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e47
              have b13e113 : x = (M.op y x) := by
                first
                | (have i₁ := b13e28
                   have i₂ := b13e58 y
                   grind)
                | exact superpose b13e58 b13e28
                | exact resolve b13e28 b13e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e58
              have b13e120 : x = y := by
                first
                | (have i₁ := b13e113
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e113
                | exact resolve b13e113 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e113
              have b13e124 : False := by grind
              exact b13e124
            · have b14e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op y x) := by grind
              have b14e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e45 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (σ y) (σ x) X1
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e15
                | exact resolve b14e15 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e46 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 y x X1
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e52 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 y X1 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e55 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b14e46 X0 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e46
                | exact resolve b14e46 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e86 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op y X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 X0 y X2
                   have i₂ := b14e55 X0
                   grind)
                | (have i₁ := b14e15 X0 y X0 x
                   have i₂ := b14e55 X0
                   grind)
                | exact superpose b14e55 b14e15
                | exact resolve b14e15 b14e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e90 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 y) X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e46 X1 X0
                   have i₂ := b14e55 X0
                   grind)
                | (have i₁ := b14e46 X0 y
                   have i₂ := b14e55 y
                   grind)
                | exact superpose b14e55 b14e46
                | exact resolve b14e46 b14e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e46
              have b14e97 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e86 X0 X1 X2
                   have i₂ := b14e52 X1 X0
                   grind)
                | exact superpose b14e52 b14e86
                | exact resolve b14e86 b14e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e52 b14e86
              have b14e223 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e45 X0 (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e45
                | exact resolve b14e45 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e225 : ∀ X0 X1 X3 : G, (M.op X3 (σ y)) = (M.op (M.op (M.op X0 X1) (σ y)) X3) := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e45 X3 (M.op X0 x)
                   have i₂ := b14e15 (σ y) X0 x X1
                   grind)
                | exact superpose b14e15 b14e45
                | exact resolve b14e45 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e238 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e90 (σ y) X0
                   have i₂ := b14e45 X0 y
                   grind)
                | exact superpose b14e45 b14e90
                | exact resolve b14e90 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e45 b14e90
              have b14e265 : ∀ X3 : G, (M.op y X3) = (M.op X3 (σ y)) := by
                intro X3
                first
                | (have i₁ := b14e225 x x X3
                   have i₂ := b14e97 (M.op x x) X3 (σ y)
                   grind)
                | exact superpose b14e97 b14e225
                | exact resolve b14e225 b14e97
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e97 b14e225
              have b14e267 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b14e223 X0
                   have i₂ := b14e238 X0
                   grind)
                | exact superpose b14e238 b14e223
                | exact resolve b14e223 b14e238
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e223 b14e238
              have b14e291 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e265 (σ x)
                   grind)
                | exact superpose b14e265 b14e22
                | exact resolve b14e22 b14e265
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e265
              have b14e299 : (M.op y (σ x)) ≠ (σ (M.op y x)) := by
                first
                | (have i₁ := b14e291
                   have i₂ := b14e55 x
                   grind)
                | exact superpose b14e55 b14e291
                | exact resolve b14e291 b14e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e291
              have b14e311 : (σ y) ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b14e299
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e299
                | exact resolve b14e299 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e299
              have b14e565 : (σ y) = (M.op (σ x) y) := by
                first
                | (have i₁ := b14e26
                   have i₂ := b14e267 (σ x)
                   grind)
                | exact superpose b14e267 b14e26
                | exact resolve b14e26 b14e267
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e267
              have b14e595 : (σ y) = (M.op y (σ x)) := by
                first
                | (have i₁ := b14e565
                   have i₂ := b14e55 (σ x)
                   grind)
                | exact superpose b14e55 b14e565
                | exact resolve b14e565 b14e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e55 b14e565
              have b14e608 : False := by grind
              exact b14e608
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b15e24 : (σ x) ≠ (σ y) := by grind
            have b15e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e33 : False := by grind
            exact b15e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b16e24 : y = (M.op y x) := by grind
              have b16e27 : x ≠ y := by grind
              have b16e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e46 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 x y X1
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e56 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b16e46 X0 y
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e46
                | exact resolve b16e46 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e46
              have b16e107 : x = (M.op y x) := by
                first
                | (have i₁ := b16e28
                   have i₂ := b16e56 y
                   grind)
                | exact superpose b16e56 b16e28
                | exact resolve b16e28 b16e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e56
              have b16e114 : x = y := by
                first
                | (have i₁ := b16e107
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e107
                | exact resolve b16e107 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e107
              have b16e118 : False := by grind
              exact b16e118
            · have b17e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e24 : y = (M.op y x) := by grind
              have b17e25 : (σ x) ≠ (σ y) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e27 : x ≠ y := by grind
              have b17e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 (τ X0) X1
                   have i₂ := b17e17 X0
                   grind)
                | exact superpose b17e17 b17e21
                | exact resolve b17e21 b17e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 (τ X0)
                   have i₂ := b17e17 X0
                   grind)
                | exact superpose b17e17 b17e21
                | exact resolve b17e21 b17e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b17e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b17e33
              have b17e37 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                grind
              clear b17e30
              have b17e41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b17e37 X0
                   have i₂ := b17e17 X0
                   grind)
                | exact superpose b17e17 b17e37
                | exact resolve b17e37 b17e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37
              have b17e42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                grind
              clear b17e41
              have b17e43 : ∀ X0 X1 : G, (M.op (M.op y X1) X0) = (M.op X0 y) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 y x X1
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e48 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op y X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 y X1 x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e53 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b17e43 X0 x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e43
                | exact resolve b17e43 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e67 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = X0 ∨ (k X0 (M.op X1 X3)) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e19 X0 (M.op X1 X3)
                   have i₂ := b17e15 X0 X1 X2 X3
                   grind)
                | (have i₁ := b17e19 (M.op X1 X2) X0
                   have i₂ := b17e15 X0 X1 X2 X3
                   grind)
                | exact superpose b17e15 b17e19
                | (have j0 := b17e19 (M.op X1 X3) X0
                   grind)
                | (have r₁ := b17e19 X0 (M.op X0 (M.op X0 X2))
                   have r₂ := b17e15 X0 X0 X2 (M.op X0 X2)
                   grind)
                | exact resolve b17e19 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X1 X0
                   have i₂ := b17e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e79 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X0 X2 y
                   have i₂ := b17e53 X0
                   grind)
                | (have i₁ := b17e15 X0 y X2 X0
                   have i₂ := b17e53 X0
                   grind)
                | exact superpose b17e53 b17e15
                | exact resolve b17e15 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e80 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op y X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X0 y X2
                   have i₂ := b17e53 X0
                   grind)
                | (have i₁ := b17e15 X0 y X0 x
                   have i₂ := b17e53 X0
                   grind)
                | exact superpose b17e53 b17e15
                | exact resolve b17e15 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e86 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) X1) = (M.op X1 (M.op y X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 y X2 X0
                   have i₂ := b17e53 X0
                   grind)
                | (have i₁ := b17e15 X0 X0 X2 y
                   have i₂ := b17e53 X0
                   grind)
                | exact superpose b17e53 b17e15
                | exact resolve b17e15 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e89 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e86 X0 X1 x
                   have i₂ := b17e48 X1 x
                   grind)
                | exact superpose b17e48 b17e86
                | exact resolve b17e86 b17e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e86
              have b17e91 : ∀ X0 X1 X2 : G, (M.op y X1) = (M.op (M.op X0 X2) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e80 X0 X1 X2
                   have i₂ := b17e48 X1 X0
                   grind)
                | exact superpose b17e48 b17e80
                | exact resolve b17e80 b17e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e48 b17e80
              have b17e92 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e79 X0 X1 X2
                   have i₂ := b17e43 X1 X0
                   grind)
                | exact superpose b17e43 b17e79
                | exact resolve b17e79 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e79
              have b17e145 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e16 (k X0 (τ X1))
                   have i₂ := b17e31 X1 X0
                   grind)
                | exact superpose b17e31 b17e16
                | exact resolve b17e16 b17e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e371 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X0 X1 X2 y
                   have i₂ := b17e89 X1 X0
                   grind)
                | exact superpose b17e89 b17e15
                | exact resolve b17e15 b17e89
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e89
              have b17e3435 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e34 (M.op (τ X0) (τ X0))
                   have i₂ := b17e42 X0
                   grind)
                | exact superpose b17e42 b17e34
                | exact resolve b17e34 b17e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e3438 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e16 (M.op (τ X0) (τ X0))
                   have i₂ := b17e42 X0
                   grind)
                | exact superpose b17e42 b17e16
                | exact resolve b17e16 b17e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e42
              have b17e3441 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have i₁ := b17e3435 X0
                   have i₂ := b17e92 X0 (M.op X0 X0) X0
                   grind)
                | exact superpose b17e92 b17e3435
                | exact resolve b17e3435 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3435
              have b17e3443 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op y (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b17e3441 X0
                   have i₂ := b17e53 (M.op X0 X0)
                   grind)
                | exact superpose b17e53 b17e3441
                | exact resolve b17e3441 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3441
              have b17e3444 : ∀ X0 : G, (M.op y y) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
                intro X0
                first
                | (have i₁ := b17e3443 X0
                   have i₂ := b17e92 X0 y X0
                   grind)
                | exact superpose b17e92 b17e3443
                | exact resolve b17e3443 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3443
              have b17e3445 : ∀ X0 : G, (M.op y y) = (σ (M.op (M.op (τ X0) (τ X0)) y)) := by
                intro X0
                first
                | (have i₁ := b17e3444 X0
                   have i₂ := b17e92 (τ X0) (M.op (τ X0) (τ X0)) (τ X0)
                   grind)
                | exact superpose b17e92 b17e3444
                | exact resolve b17e3444 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3444
              have b17e3446 : ∀ X0 : G, (M.op y y) = (σ (M.op y (M.op (τ X0) (τ X0)))) := by
                intro X0
                first
                | (have i₁ := b17e3445 X0
                   have i₂ := b17e53 (M.op (τ X0) (τ X0))
                   grind)
                | exact superpose b17e53 b17e3445
                | exact resolve b17e3445 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3445
              have b17e3447 : (M.op y y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b17e3446 x
                   have i₂ := b17e92 (τ x) y (τ x)
                   grind)
                | exact superpose b17e92 b17e3446
                | exact resolve b17e3446 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3446
              have b17e3583 : (M.op y y) = (τ (M.op y y)) := by
                first
                | (have i₁ := b17e16 (M.op y y)
                   have i₂ := b17e3447
                   grind)
                | exact superpose b17e3447 b17e16
                | exact resolve b17e16 b17e3447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e3670 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b17e67 X0 X0 x (M.op X0 X1)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e67
              have b17e3671 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b17e3670 X0 X1
                   have i₂ := b17e92 X0 X0 X1
                   grind)
                | exact superpose b17e92 b17e3670
                | (have j0 := b17e3670 X0 X1
                   grind)
                | exact resolve b17e3670 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3670
              have b17e3738 : ∀ X0 : G, (k X0 (M.op X0 y)) = X0 ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have i₁ := b17e3671 X0 x
                   have i₂ := b17e92 X0 X0 x
                   grind)
                | exact superpose b17e92 b17e3671
                | (have j0 := b17e3671 X0 x
                   grind)
                | exact resolve b17e3671 b17e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3671
              have b17e3813 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b17e22
                   have i₂ := b17e73 x y
                   grind)
                | exact superpose b17e73 b17e22
                | (have j1 := b17e73 x y
                   grind)
                | exact resolve b17e22 b17e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e73
              have b17e3862 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b17e3813
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e3813 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3813
              have b17e3874 : (σ (k y x)) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e3862
                   have i₂ := b17e53 x
                   grind)
                | exact superpose b17e53 b17e3862
                | exact resolve b17e3862 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3862
              have b17e3883 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e3874
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e3874
                | exact resolve b17e3874 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3874
              have b17e3902 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (M.op y y) X0)) := by
                intro X0
                first
                | (have i₁ := b17e145 (M.op y y) X0
                   have i₂ := b17e3447
                   grind)
                | exact superpose b17e3447 b17e145
                | exact resolve b17e145 b17e3447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e4908 : ∀ X0 X1 : G, (M.op y X1) = (M.op (τ (M.op X0 X0)) X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e91 (τ X0) X1 (τ X0)
                   have i₂ := b17e3438 X0
                   grind)
                | exact superpose b17e3438 b17e91
                | exact resolve b17e91 b17e3438
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e4911 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (τ (M.op X0 X0))) := by
                intro X0 X1
                first
                | (have i₁ := b17e371 X1 (τ X0) (τ X0)
                   have i₂ := b17e3438 X0
                   grind)
                | exact superpose b17e3438 b17e371
                | exact resolve b17e371 b17e3438
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3438
              have b17e5780 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) y))) ∨ (σ X0) = (M.op (σ X0) y) := by
                intro X0
                first
                | (have i₁ := b17e145 X0 (M.op (σ X0) y)
                   have i₂ := b17e3738 (σ X0)
                   grind)
                | exact superpose b17e3738 b17e145
                | (have j1 := b17e3738 (σ X0)
                   grind)
                | exact resolve b17e145 b17e3738
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3738
              have b17e5785 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op y (σ X0)))) ∨ (σ X0) = (M.op (σ X0) y) := by
                intro X0
                first
                | (have i₁ := b17e5780 X0
                   have i₂ := b17e53 (σ X0)
                   grind)
                | exact superpose b17e53 b17e5780
                | (have j0 := b17e5780 X0
                   grind)
                | exact resolve b17e5780 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e5780
              have b17e5797 : ∀ X0 : G, (k X0 (τ (M.op y (σ X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) y) := by
                intro X0
                first
                | (have i₁ := b17e5785 X0
                   have i₂ := b17e16 X0
                   grind)
                | exact superpose b17e16 b17e5785
                | (have j0 := b17e5785 X0
                   grind)
                | exact resolve b17e5785 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e5785
              have b17e5807 : ∀ X0 : G, (k X0 (τ (M.op y (σ X0)))) = X0 ∨ (σ X0) = (M.op y (σ X0)) := by
                intro X0
                first
                | (have i₁ := b17e5797 X0
                   have i₂ := b17e53 (σ X0)
                   grind)
                | exact superpose b17e53 b17e5797
                | (have j0 := b17e5797 X0
                   grind)
                | exact resolve b17e5797 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e5797
              have b17e7487 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b17e3883
                   have i₂ := b17e20 y x
                   grind)
                | exact superpose b17e20 b17e3883
                | (have j1 := b17e20 y x
                   grind)
                | (have r₁ := b17e3883
                   have r₂ := b17e20 (σ y) (σ (k y x))
                   grind)
                | (have r₁ := b17e3883
                   have r₂ := b17e20 (σ (k y x)) (σ y)
                   grind)
                | exact resolve b17e3883 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3883
              have b17e7488 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
                first
                | (have r₁ := b17e7487
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e7487 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7487
              have b17e7489 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b17e7488
                   have r₂ := b17e27
                   grind)
                | exact resolve b17e7488 b17e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7488
              have b17e7490 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e7489
                   have i₂ := b17e53 x
                   grind)
                | exact superpose b17e53 b17e7489
                | exact resolve b17e7489 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7489
              have b17e7491 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e7490
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e7490
                | exact resolve b17e7490 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7490
              have b17e7492 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear b17e7491
              have b17e7497 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b17e19 (σ y) (σ x)
                   have i₂ := b17e7492
                   grind)
                | exact superpose b17e7492 b17e19
                | (have j0 := b17e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b17e19 (σ y) (σ x)
                   have r₂ := b17e7492
                   grind)
                | exact resolve b17e19 b17e7492
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e7515 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b17e91 (σ x) X0 (σ y)
                   have i₂ := b17e7492
                   grind)
                | exact superpose b17e7492 b17e91
                | exact resolve b17e91 b17e7492
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e91
              have b17e7516 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e92 (σ x) X0 (σ y)
                   have i₂ := b17e7492
                   grind)
                | exact superpose b17e7492 b17e92
                | exact resolve b17e92 b17e7492
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e92
              have b17e7518 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e371 X0 (σ x) (σ y)
                   have i₂ := b17e7492
                   grind)
                | exact superpose b17e7492 b17e371
                | exact resolve b17e371 b17e7492
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e371
              have b17e7519 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
              clear b17e7497
              have b17e7536 : (σ y) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b17e7519
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e7519 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7519
              have b17e7545 : (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b17e7536
                   have i₂ := b17e21 y x
                   grind)
                | exact superpose b17e21 b17e7536
                | exact resolve b17e7536 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7536
              have b17e7603 : (k y x) = (τ (σ y)) := by
                first
                | (have i₁ := b17e16 (k y x)
                   have i₂ := b17e7545
                   grind)
                | exact superpose b17e7545 b17e16
                | exact resolve b17e16 b17e7545
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7545
              have b17e7633 : y = (k y x) := by
                first
                | (have i₁ := b17e7603
                   have i₂ := b17e16 y
                   grind)
                | exact superpose b17e16 b17e7603
                | exact resolve b17e7603 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7603
              have b17e7788 : (σ x) = (M.op y (σ y)) := by
                first
                | (have i₁ := b17e7492
                   have i₂ := b17e7515 (σ y)
                   grind)
                | exact superpose b17e7515 b17e7492
                | exact resolve b17e7492 b17e7515
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e7790 : (σ (M.op x x)) = (M.op y (σ x)) := by
                first
                | (have i₁ := b17e34 x
                   have i₂ := b17e7515 (σ x)
                   grind)
                | exact superpose b17e7515 b17e34
                | exact resolve b17e34 b17e7515
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e34
              have b17e7906 : (M.op y y) = (σ (M.op x x)) := by
                first
                | (have i₁ := b17e7790
                   have i₂ := b17e7518 y
                   grind)
                | exact superpose b17e7518 b17e7790
                | exact resolve b17e7790 b17e7518
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7790
              have b17e8832 : ∀ X0 : G, (τ (k (M.op y y) X0)) = (k (M.op x x) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b17e145 (M.op x x) X0
                   have i₂ := b17e7906
                   grind)
                | exact superpose b17e7906 b17e145
                | exact resolve b17e145 b17e7906
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e145
              have b17e8833 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (k (M.op x x) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b17e8832 X0
                   have i₂ := b17e3902 X0
                   grind)
                | exact superpose b17e3902 b17e8832
                | exact resolve b17e8832 b17e3902
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3902 b17e8832
              have b17e17001 : x = (k x (τ (M.op y y))) ∨ (σ x) = (M.op y y) := by
                first
                | (have i₁ := b17e5807 x
                   have i₂ := b17e7516 y
                   grind)
                | exact superpose b17e7516 b17e5807
                | exact resolve b17e5807 b17e7516
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e5807 b17e7516
              have b17e17051 : x = (k x (M.op y y)) ∨ (σ x) = (M.op y y) := by
                first
                | (have i₁ := b17e17001
                   have i₂ := b17e3583
                   grind)
                | exact superpose b17e3583 b17e17001
                | exact resolve b17e17001 b17e3583
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e17001
              have b17e20259 : x = (M.op (M.op y y) x) ∨ (M.op y y) = (M.op (M.op y y) x) ∨ x = (M.op y y) ∨ (σ x) = (M.op y y) := by
                first
                | (have i₁ := b17e20 x (M.op y y)
                   have i₂ := b17e17051
                   grind)
                | exact superpose b17e17051 b17e20
                | (have j0 := b17e20 x (M.op y y)
                   grind)
                | exact resolve b17e20 b17e17051
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e17051
              have b17e20269 : x = (M.op x y) ∨ (M.op y y) = (M.op (M.op y y) x) ∨ x = (M.op y y) ∨ (σ x) = (M.op y y) := by
                first
                | (have i₁ := b17e20259
                   have i₂ := b17e43 x y
                   grind)
                | exact superpose b17e43 b17e20259
                | exact resolve b17e20259 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e20259
              have b17e20272 : (M.op y y) = (M.op (M.op y y) x) ∨ x = (M.op y y) ∨ (σ x) = (M.op y y) := by
                first
                | (have r₁ := b17e20269
                   have r₂ := b17e28
                   grind)
                | exact resolve b17e20269 b17e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e20269
              have b17e20275 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op y y) := by
                first
                | (have i₁ := b17e20272
                   have i₂ := b17e43 x y
                   grind)
                | exact superpose b17e43 b17e20272
                | exact resolve b17e20272 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e43 b17e20272
              have b17e20278 : (M.op y x) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op y y) := by
                first
                | (have i₁ := b17e20275
                   have i₂ := b17e53 x
                   grind)
                | exact superpose b17e53 b17e20275
                | exact resolve b17e20275 b17e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e53 b17e20275
              have b17e20281 : (σ x) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b17e20278
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e20278
                | exact resolve b17e20278 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e20278
              have b17e46644 : (σ x) = (τ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b17e3583
                   have i₂ := b17e20281
                   grind)
                | exact superpose b17e20281 b17e3583
                | exact resolve b17e3583 b17e20281
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e46759 : x ≠ (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b17e20281
              have b17e46822 : x = (σ x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b17e46644
                   have i₂ := b17e16 x
                   grind)
                | exact superpose b17e16 b17e46644
                | exact resolve b17e46644 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46644
              have b17e46832 : x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have r₁ := b17e46822
                   have r₂ := b17e46759
                   grind)
                | exact resolve b17e46822 b17e46759
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46759 b17e46822
              have b17e47008 : y = (M.op y y) ∨ x = (σ x) := by
                first
                | (have i₁ := b17e3447
                   have i₂ := b17e46832
                   grind)
                | exact superpose b17e46832 b17e3447
                | exact resolve b17e3447 b17e46832
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e47012 : y = (M.op y y) ∨ x = (τ x) := by
                first
                | (have i₁ := b17e3583
                   have i₂ := b17e46832
                   grind)
                | exact superpose b17e46832 b17e3583
                | exact resolve b17e3583 b17e46832
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3583
              have b17e47330 : x = (σ x) ∨ y = (σ y) := by
                first
                | (have i₁ := b17e3447
                   have i₂ := b17e47008
                   grind)
                | exact superpose b17e47008 b17e3447
                | exact resolve b17e3447 b17e47008
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e47711 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ y = (σ y) := by
                intro X0
                first
                | (have i₁ := b17e7515 X0
                   have i₂ := b17e47330
                   grind)
                | exact superpose b17e47330 b17e7515
                | exact resolve b17e7515 b17e47330
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7515 b17e47330
              have b17e54473 : x ≠ (M.op y y) ∨ y = (σ y) := by
                first
                | (have i₁ := b17e28
                   have i₂ := b17e47711 y
                   grind)
                | exact superpose b17e47711 b17e28
                | exact resolve b17e28 b17e47711
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e47711
              have b17e55225 : x ≠ x ∨ y = (σ y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b17e54473
                   have i₂ := b17e46832
                   grind)
                | exact superpose b17e46832 b17e54473
                | (have r₁ := b17e54473
                   have r₂ := b17e46832
                   grind)
                | exact resolve b17e54473 b17e46832
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46832 b17e54473
              have b17e55227 : y = (M.op y y) ∨ y = (σ y) := by grind
              clear b17e55225
              have b17e55675 : y = (σ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b17e3447
                   have i₂ := b17e55227
                   grind)
                | exact superpose b17e55227 b17e3447
                | exact resolve b17e3447 b17e55227
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e3447 b17e55227
              have b17e55803 : y = (σ y) := by grind
              clear b17e55675
              have b17e56207 : y ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e55803
                   grind)
                | exact superpose b17e55803 b17e26
                | exact resolve b17e26 b17e55803
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e56209 : (σ x) = (M.op y y) := by
                first
                | (have i₁ := b17e7788
                   have i₂ := b17e55803
                   grind)
                | exact superpose b17e55803 b17e7788
                | exact resolve b17e7788 b17e55803
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7788
              have b17e56273 : y ≠ (M.op y y) := by
                first
                | (have i₁ := b17e56207
                   have i₂ := b17e7518 y
                   grind)
                | exact superpose b17e7518 b17e56207
                | exact resolve b17e56207 b17e7518
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7518 b17e56207
              have b17e56277 : y ≠ (σ x) := by
                first
                | (have i₁ := b17e56273
                   have i₂ := b17e56209
                   grind)
                | exact superpose b17e56209 b17e56273
                | exact resolve b17e56273 b17e56209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56273
              have b17e57813 : y = (σ x) ∨ x = (σ x) := by
                first
                | (have i₁ := b17e47008
                   have i₂ := b17e56209
                   grind)
                | exact superpose b17e56209 b17e47008
                | exact resolve b17e47008 b17e56209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e47008
              have b17e57814 : y = (σ x) ∨ x = (τ x) := by
                first
                | (have i₁ := b17e47012
                   have i₂ := b17e56209
                   grind)
                | exact superpose b17e56209 b17e47012
                | exact resolve b17e47012 b17e56209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e47012
              have b17e57859 : ∀ X0 : G, (M.op y X0) = (M.op (τ (σ x)) X0) := by
                intro X0
                first
                | (have i₁ := b17e4908 y X0
                   have i₂ := b17e56209
                   grind)
                | exact superpose b17e56209 b17e4908
                | exact resolve b17e4908 b17e56209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4908
              have b17e57862 : ∀ X0 : G, (M.op y X0) = (M.op X0 (τ (σ x))) := by
                intro X0
                first
                | (have i₁ := b17e4911 y X0
                   have i₂ := b17e56209
                   grind)
                | exact superpose b17e56209 b17e4911
                | exact resolve b17e4911 b17e56209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e4911
              have b17e57975 : ∀ X0 : G, (M.op y X0) = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b17e57862 X0
                   have i₂ := b17e16 x
                   grind)
                | exact superpose b17e16 b17e57862
                | exact resolve b17e57862 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57862
              have b17e57978 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b17e57859 X0
                   have i₂ := b17e16 x
                   grind)
                | exact superpose b17e16 b17e57859
                | exact resolve b17e57859 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57859
              have b17e57991 : x = (τ x) := by
                first
                | (have r₁ := b17e57814
                   have r₂ := b17e56277
                   grind)
                | exact resolve b17e57814 b17e56277
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57814
              have b17e57992 : x = (σ x) := by
                first
                | (have r₁ := b17e57813
                   have r₂ := b17e56277
                   grind)
                | exact resolve b17e57813 b17e56277
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56277 b17e57813
              have b17e58465 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
                intro X0
                first
                | (have i₁ := b17e31 x X0
                   have i₂ := b17e57991
                   grind)
                | exact superpose b17e57991 b17e31
                | exact resolve b17e31 b17e57991
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e31
              have b17e58529 : (k (M.op y y) x) = (k (M.op x x) x) := by
                first
                | (have i₁ := b17e8833 x
                   have i₂ := b17e57991
                   grind)
                | exact superpose b17e57991 b17e8833
                | exact resolve b17e8833 b17e57991
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e8833 b17e57991
              have b17e58542 : (k (M.op y y) x) = (k (M.op y x) x) := by
                first
                | (have i₁ := b17e58529
                   have i₂ := b17e57975 x
                   grind)
                | exact superpose b17e57975 b17e58529
                | exact resolve b17e58529 b17e57975
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57975 b17e58529
              have b17e58560 : (k y x) = (k (M.op y y) x) := by
                first
                | (have i₁ := b17e58542
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e58542
                | exact resolve b17e58542 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58542
              have b17e58576 : (k y x) = (k (σ x) x) := by
                first
                | (have i₁ := b17e58560
                   have i₂ := b17e56209
                   grind)
                | exact superpose b17e56209 b17e58560
                | exact resolve b17e58560 b17e56209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56209 b17e58560
              have b17e58590 : (k y x) = (σ (k x x)) := by
                first
                | (have i₁ := b17e58576
                   have i₂ := b17e58465 x
                   grind)
                | exact superpose b17e58465 b17e58576
                | exact resolve b17e58576 b17e58465
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58465 b17e58576
              have b17e58592 : (k y x) = (σ (M.op x x)) := by grind
              clear b17e58590
              have b17e58594 : (M.op y y) = (k y x) := by
                first
                | (have i₁ := b17e58592
                   have i₂ := b17e7906
                   grind)
                | exact superpose b17e7906 b17e58592
                | exact resolve b17e58592 b17e7906
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7906 b17e58592
              have b17e58596 : y = (M.op y y) := by
                first
                | (have i₁ := b17e58594
                   have i₂ := b17e7633
                   grind)
                | exact superpose b17e7633 b17e58594
                | exact resolve b17e58594 b17e7633
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7633 b17e58594
              have b17e59073 : x = (M.op x (σ y)) := by
                first
                | (have i₁ := b17e7492
                   have i₂ := b17e57992
                   grind)
                | exact superpose b17e57992 b17e7492
                | exact resolve b17e7492 b17e57992
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e7492 b17e57992
              have b17e59153 : x = (M.op y (σ y)) := by
                first
                | (have i₁ := b17e59073
                   have i₂ := b17e57978 (σ y)
                   grind)
                | exact superpose b17e57978 b17e59073
                | exact resolve b17e59073 b17e57978
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57978 b17e59073
              have b17e59173 : x = (M.op y y) := by
                first
                | (have i₁ := b17e59153
                   have i₂ := b17e55803
                   grind)
                | exact superpose b17e55803 b17e59153
                | exact resolve b17e59153 b17e55803
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e55803 b17e59153
              have b17e59187 : x = y := by
                first
                | (have i₁ := b17e59173
                   have i₂ := b17e58596
                   grind)
                | exact superpose b17e58596 b17e59173
                | exact resolve b17e59173 b17e58596
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e58596 b17e59173
              have b17e59192 : False := by grind
              exact b17e59192
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b18e21 : x ≠ y := by grind
          have b18e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e30 : False := by grind
          exact b18e30
        · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e24 : (σ x) = (σ y) := by grind
            have b19e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 y
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e15
              | exact resolve b19e15 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e31 : x = y := by
              first
              | (have i₁ := b19e30
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e30
              | exact resolve b19e30 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : False := by grind
            exact b19e32
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e24 : (σ x) = (σ y) := by grind
            have b20e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e29 : y = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 y
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e15
              | exact resolve b20e15 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e30 : x = y := by
              first
              | (have i₁ := b20e29
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e29
              | exact resolve b20e29 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : False := by grind
            exact b20e31
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b21e24 : (σ x) ≠ (σ y) := by grind
            have b21e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e33 : False := by grind
            exact b21e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b22e24 : y ≠ (M.op y x) := by grind
              have b22e25 : (σ x) ≠ (σ y) := by grind
              have b22e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b22e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b22e22
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e22
                | exact resolve b22e22 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b22e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b22e34
              have b22e46 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 (σ y) (σ x) X1
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e15
                | exact resolve b22e15 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e47 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 x y X1
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e48 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
                intro X0 X1 X2 X4
                first
                | (have i₁ := b22e15 X2 X0 x X4
                   have i₂ := b22e15 X2 X0 x X1
                   grind)
                | (have i₁ := b22e15 (M.op X1 x) X1 X2 x
                   have i₂ := b22e15 (M.op X1 X2) X1 X2 x
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e53 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 x X1 y
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e56 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b22e47 X0 y
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e47
                | exact resolve b22e47 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e69 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = X0 ∨ (k X0 (M.op X1 X3)) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e19 X0 (M.op X1 X3)
                   have i₂ := b22e15 X0 X1 X2 X3
                   grind)
                | (have i₁ := b22e19 (M.op X1 X2) X0
                   have i₂ := b22e15 X0 X1 X2 X3
                   grind)
                | exact superpose b22e15 b22e19
                | (have j0 := b22e19 (M.op X1 X3) X0
                   grind)
                | (have r₁ := b22e19 X0 (M.op X0 (M.op X0 X2))
                   have r₂ := b22e15 X0 X0 X2 (M.op X0 X2)
                   grind)
                | exact resolve b22e19 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e100 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e15 X1 X0 X2 (M.op x x)
                   have i₂ := b22e53 X0 x
                   grind)
                | exact superpose b22e53 b22e15
                | exact resolve b22e15 b22e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e101 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X1) = (M.op X1 (M.op x X0)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b22e15 X1 X0 (M.op x x) X3
                   have i₂ := b22e53 X0 x
                   grind)
                | exact superpose b22e53 b22e15
                | exact resolve b22e15 b22e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e106 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op X0 X3) X1) := by
                intro X0 X1 X3
                first
                | (have i₁ := b22e101 X0 X1 X3
                   have i₂ := b22e53 X1 X0
                   grind)
                | exact superpose b22e53 b22e101
                | exact resolve b22e101 b22e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e101
              have b22e107 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e100 X0 X1 X2
                   have i₂ := b22e47 X1 X0
                   grind)
                | exact superpose b22e47 b22e100
                | exact resolve b22e100 b22e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e47 b22e100
              have b22e163 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b22e46 X0 (σ x)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e46
                | exact resolve b22e46 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e172 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 (σ y) X1 x
                   have i₂ := b22e46 X0 x
                   grind)
                | exact superpose b22e46 b22e15
                | exact resolve b22e15 b22e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e46
              have b22e184 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b22e172 X0 x
                   have i₂ := b22e107 (σ y) X0 x
                   grind)
                | exact superpose b22e107 b22e172
                | exact resolve b22e172 b22e107
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e172
              have b22e236 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) X0) X1) := by
                intro X0 X1
                first
                | (have i₁ := b22e48 (σ y) X0 X1 (σ x)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e48
                | exact resolve b22e48 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e48
              have b22e281 : ∀ X1 : G, (M.op (σ y) X1) = (M.op x X1) := by
                intro X1
                first
                | (have i₁ := b22e236 x X1
                   have i₂ := b22e106 (σ y) X1 x
                   grind)
                | exact superpose b22e106 b22e236
                | exact resolve b22e236 b22e106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e236
              have b22e340 : (σ x) ≠ (M.op (σ x) x) := by
                first
                | (have i₁ := b22e30
                   have i₂ := b22e184 (σ x)
                   grind)
                | exact superpose b22e184 b22e30
                | exact resolve b22e30 b22e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e30
              have b22e341 : (σ (M.op y y)) = (M.op (σ y) x) := by
                first
                | (have i₁ := b22e35 y
                   have i₂ := b22e184 (σ y)
                   grind)
                | exact superpose b22e184 b22e35
                | exact resolve b22e35 b22e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e345 : (σ (M.op y y)) = (M.op x (σ y)) := by
                first
                | (have i₁ := b22e341
                   have i₂ := b22e163 x
                   grind)
                | exact superpose b22e163 b22e341
                | exact resolve b22e341 b22e163
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e163 b22e341
              have b22e346 : (σ x) ≠ (M.op x (σ x)) := by
                first
                | (have i₁ := b22e340
                   have i₂ := b22e56 (σ x)
                   grind)
                | exact superpose b22e56 b22e340
                | exact resolve b22e340 b22e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e340
              have b22e358 : (M.op x x) = (σ (M.op y y)) := by
                first
                | (have i₁ := b22e345
                   have i₂ := b22e184 x
                   grind)
                | exact superpose b22e184 b22e345
                | exact resolve b22e345 b22e184
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e345
              have b22e2303 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op x x) (M.op x x)) := by
                first
                | (have i₁ := b22e35 (M.op y y)
                   have i₂ := b22e358
                   grind)
                | exact superpose b22e358 b22e35
                | exact resolve b22e35 b22e358
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e35
              have b22e2304 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op x x)) := by
                intro X0
                first
                | (have i₁ := b22e21 X0 (M.op y y)
                   have i₂ := b22e358
                   grind)
                | exact superpose b22e358 b22e21
                | exact resolve b22e21 b22e358
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e2306 : (M.op y y) = (τ (M.op x x)) := by
                first
                | (have i₁ := b22e16 (M.op y y)
                   have i₂ := b22e358
                   grind)
                | exact superpose b22e358 b22e16
                | exact resolve b22e16 b22e358
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e358
              have b22e2307 : (σ (M.op (M.op y y) (M.op y y))) = (M.op x (M.op x x)) := by
                first
                | (have i₁ := b22e2303
                   have i₂ := b22e53 (M.op x x) x
                   grind)
                | exact superpose b22e53 b22e2303
                | exact resolve b22e2303 b22e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2303
              have b22e2308 : (M.op x x) = (σ (M.op (M.op y y) (M.op y y))) := by
                first
                | (have i₁ := b22e2307
                   have i₂ := b22e53 x x
                   grind)
                | exact superpose b22e53 b22e2307
                | exact resolve b22e2307 b22e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e53 b22e2307
              have b22e2309 : (M.op x x) = (σ (M.op (M.op y y) x)) := by
                first
                | (have i₁ := b22e2308
                   have i₂ := b22e107 y (M.op y y) y
                   grind)
                | exact superpose b22e107 b22e2308
                | exact resolve b22e2308 b22e107
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2308
              have b22e2310 : (M.op x x) = (σ (M.op x (M.op y y))) := by
                first
                | (have i₁ := b22e2309
                   have i₂ := b22e56 (M.op y y)
                   grind)
                | exact superpose b22e56 b22e2309
                | exact resolve b22e2309 b22e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e56 b22e2309
              have b22e2311 : (M.op x x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b22e2310
                   have i₂ := b22e107 y x y
                   grind)
                | exact superpose b22e107 b22e2310
                | exact resolve b22e2310 b22e107
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2310
              have b22e3303 : (M.op x x) = (τ (M.op x x)) := by
                first
                | (have i₁ := b22e16 (M.op x x)
                   have i₂ := b22e2311
                   grind)
                | exact superpose b22e2311 b22e16
                | exact resolve b22e16 b22e2311
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e3304 : (M.op x x) = (M.op y y) := by
                first
                | (have i₁ := b22e3303
                   have i₂ := b22e2306
                   grind)
                | exact superpose b22e2306 b22e3303
                | exact resolve b22e3303 b22e2306
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3303
              have b22e3386 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
                intro X0 X1
                first
                | (have j0 := b22e69 X0 X0 x (M.op X0 X1)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e69
              have b22e3387 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b22e3386 X0 X1
                   have i₂ := b22e107 X0 X0 X1
                   grind)
                | exact superpose b22e107 b22e3386
                | (have j0 := b22e3386 X0 X1
                   grind)
                | exact resolve b22e3386 b22e107
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3386
              have b22e3454 : ∀ X0 : G, (k X0 (M.op X0 x)) = X0 ∨ (M.op X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b22e3387 X0 x
                   have i₂ := b22e107 X0 X0 x
                   grind)
                | exact superpose b22e107 b22e3387
                | (have j0 := b22e3387 X0 x
                   grind)
                | exact resolve b22e3387 b22e107
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e107 b22e3387
              have b22e3515 : (M.op y y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b22e2311
                   have i₂ := b22e3304
                   grind)
                | exact superpose b22e3304 b22e2311
                | exact resolve b22e2311 b22e3304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e3516 : (M.op y y) = (τ (M.op y y)) := by
                first
                | (have i₁ := b22e2306
                   have i₂ := b22e3304
                   grind)
                | exact superpose b22e3304 b22e2306
                | exact resolve b22e2306 b22e3304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2306
              have b22e7309 : (σ y) = (k (σ y) (M.op x x)) ∨ (σ y) = (M.op x x) := by
                first
                | (have i₁ := b22e3454 (σ y)
                   have i₂ := b22e281 x
                   grind)
                | exact superpose b22e281 b22e3454
                | exact resolve b22e3454 b22e281
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e281 b22e3454
              have b22e7324 : (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (M.op x x) := by
                first
                | (have i₁ := b22e7309
                   have i₂ := b22e2304 y
                   grind)
                | exact superpose b22e2304 b22e7309
                | exact resolve b22e7309 b22e2304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2304 b22e7309
              have b22e7344 : (σ y) = (σ (k y (M.op y y))) ∨ (σ y) = (M.op y y) := by
                first
                | (have i₁ := b22e7324
                   have i₂ := b22e3304
                   grind)
                | exact superpose b22e3304 b22e7324
                | exact resolve b22e7324 b22e3304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e7324
              have b22e24262 : (σ y) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e7344
                   have i₂ := b22e20 y (M.op y y)
                   grind)
                | exact superpose b22e20 b22e7344
                | (have j1 := b22e20 y (M.op y y)
                   grind)
                | exact resolve b22e7344 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e7344
              have b22e24323 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e24262
                   have i₂ := b22e106 y y y
                   grind)
                | exact superpose b22e106 b22e24262
                | exact resolve b22e24262 b22e106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e24262
              have b22e24329 : (σ x) = (σ y) ∨ (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e24323
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e24323
                | exact resolve b22e24323 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e24323
              have b22e24334 : (σ y) = (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
                first
                | (have r₁ := b22e24329
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e24329 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e24329
              have b22e24338 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e24334
                   have i₂ := b22e106 y y y
                   grind)
                | exact superpose b22e106 b22e24334
                | exact resolve b22e24334 b22e106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e106 b22e24334
              have b22e24339 : (σ y) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e24338
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e24338
                | exact resolve b22e24338 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e24338
              have b22e44880 : (σ y) = (τ (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e3516
                   have i₂ := b22e24339
                   grind)
                | exact superpose b22e24339 b22e3516
                | exact resolve b22e3516 b22e24339
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3516
              have b22e44964 : y ≠ (σ y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
              clear b22e24339
              have b22e45014 : y = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e44880
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e44880
                | exact resolve b22e44880 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e44880
              have b22e45022 : x = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have r₁ := b22e45014
                   have r₂ := b22e44964
                   grind)
                | exact resolve b22e45014 b22e44964
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e44964 b22e45014
              have b22e45237 : y = (M.op y y) ∨ x = (σ x) := by
                first
                | (have i₁ := b22e3515
                   have i₂ := b22e45022
                   grind)
                | exact superpose b22e45022 b22e3515
                | exact resolve b22e3515 b22e45022
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e45641 : x = (σ x) ∨ y = (σ y) := by
                first
                | (have i₁ := b22e3515
                   have i₂ := b22e45237
                   grind)
                | exact superpose b22e45237 b22e3515
                | exact resolve b22e3515 b22e45237
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e45237
              have b22e46637 : x ≠ (M.op x x) ∨ y = (σ y) := by
                first
                | (have i₁ := b22e346
                   have i₂ := b22e45641
                   grind)
                | exact superpose b22e45641 b22e346
                | exact resolve b22e346 b22e45641
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e346 b22e45641
              have b22e46680 : x ≠ (M.op y y) ∨ y = (σ y) := by
                first
                | (have i₁ := b22e46637
                   have i₂ := b22e3304
                   grind)
                | exact superpose b22e3304 b22e46637
                | exact resolve b22e46637 b22e3304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3304 b22e46637
              have b22e49067 : x ≠ x ∨ y = (σ y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b22e46680
                   have i₂ := b22e45022
                   grind)
                | exact superpose b22e45022 b22e46680
                | (have r₁ := b22e46680
                   have r₂ := b22e45022
                   grind)
                | exact resolve b22e46680 b22e45022
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e45022 b22e46680
              have b22e49069 : y = (M.op y y) ∨ y = (σ y) := by grind
              clear b22e49067
              have b22e49193 : y = (σ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b22e3515
                   have i₂ := b22e49069
                   grind)
                | exact superpose b22e49069 b22e3515
                | exact resolve b22e3515 b22e49069
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e3515 b22e49069
              have b22e49290 : y = (σ y) := by grind
              clear b22e49193
              have b22e49455 : y = (M.op y (σ x)) := by
                first
                | (have i₁ := b22e26
                   have i₂ := b22e49290
                   grind)
                | exact superpose b22e49290 b22e26
                | exact resolve b22e26 b22e49290
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e49461 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b22e184 X0
                   have i₂ := b22e49290
                   grind)
                | exact superpose b22e49290 b22e184
                | exact resolve b22e184 b22e49290
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e184 b22e49290
              have b22e54340 : (M.op x y) = (σ (M.op x y)) := by
                first
                | (have i₁ := b22e2311
                   have i₂ := b22e49461 x
                   grind)
                | exact superpose b22e49461 b22e2311
                | exact resolve b22e2311 b22e49461
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e2311 b22e49461
              have b22e54369 : x = (σ x) := by
                first
                | (have i₁ := b22e54340
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e54340
                | exact resolve b22e54340 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e54340
              have b22e55862 : y = (M.op y x) := by
                first
                | (have i₁ := b22e49455
                   have i₂ := b22e54369
                   grind)
                | exact superpose b22e54369 b22e49455
                | exact resolve b22e49455 b22e54369
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e49455 b22e54369
              have b22e55919 : False := by grind
              exact b22e55919
            · have b23e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e25 : (σ x) ≠ (σ y) := by grind
              have b23e26 : (σ y) = (M.op (σ y) (σ x)) := by grind
              have b23e27 : x ≠ y := by grind
              have b23e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e43 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op X0 (σ y)) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 (σ y) (σ x) X1
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 X1 X0
                   have i₂ := b23e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b23e20 b23e21
                | (have j1 := b23e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b23e21 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e100 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b23e43 X0 (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e43
                | exact resolve b23e43 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e43
              have b23e3763 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b23e22
                   have i₂ := b23e78 x y
                   grind)
                | exact superpose b23e78 b23e22
                | (have j1 := b23e78 x y
                   grind)
                | exact resolve b23e22 b23e78
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e78
              have b23e3820 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b23e3763
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e3763 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3763
              have b23e3853 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have i₁ := b23e3820
                   have i₂ := b23e100 (σ x)
                   grind)
                | exact superpose b23e100 b23e3820
                | exact resolve b23e3820 b23e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e100 b23e3820
              have b23e3866 : (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have i₁ := b23e3853
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e3853
                | exact resolve b23e3853 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3853
              have b23e3875 : (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have r₁ := b23e3866
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e3866 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3866
              have b23e3909 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b23e3875
                   have i₂ := b23e20 y x
                   grind)
                | exact superpose b23e20 b23e3875
                | (have j1 := b23e20 y x
                   grind)
                | (have r₁ := b23e3875
                   have r₂ := b23e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b23e3875
                   have r₂ := b23e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b23e3875 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3875
              have b23e3910 : x = (M.op x y) ∨ x = y := by grind
              clear b23e3909
              have b23e3911 : x = y := by
                first
                | (have r₁ := b23e3910
                   have r₂ := b23e28
                   grind)
                | exact resolve b23e3910 b23e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3910
              have b23e3912 : False := by grind
              exact b23e3912
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b24e24 : (σ x) ≠ (σ y) := by grind
            have b24e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e33 : False := by grind
            exact b24e33
          · rcases eq_or_ne (M.op x y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e25 : (σ x) ≠ (σ y) := by grind
              have b25e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b25e27 : x ≠ y := by grind
              have b25e28 : x = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : (σ x) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e22
                | exact resolve b25e22 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 (τ X0) X1
                   have i₂ := b25e17 X0
                   grind)
                | exact superpose b25e17 b25e21
                | exact resolve b25e21 b25e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 (τ X0)
                   have i₂ := b25e17 X0
                   grind)
                | exact superpose b25e17 b25e21
                | exact resolve b25e21 b25e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b25e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b25e34
              have b25e38 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                grind
              clear b25e31
              have b25e42 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                first
                | (have i₁ := b25e38 X0
                   have i₂ := b25e17 X0
                   grind)
                | exact superpose b25e17 b25e38
                | exact resolve b25e38 b25e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38
              have b25e43 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
                intro X0
                grind
              clear b25e42
              have b25e44 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 x y X1
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e49 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 x X1 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X0 X1 X2 x
                   have i₂ := b25e15 X0 X1 X3 x
                   grind)
                | (have i₁ := b25e15 (M.op X1 X2) X1 X2 X3
                   have i₂ := b25e15 (M.op X1 X3) X1 X2 X3
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e54 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
                intro X0
                first
                | (have i₁ := b25e44 X0 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e44
                | exact resolve b25e44 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e66 : x ≠ x ∨ x = y ∨ y = (k y x) := by
                first
                | (have i₁ := b25e19 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e19
                | (have j0 := b25e19 x y
                   grind)
                | (have r₁ := b25e19 y x
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e19 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e68 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = X0 ∨ (k X0 (M.op X1 X3)) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e19 X0 (M.op X1 X3)
                   have i₂ := b25e15 X0 X1 X2 X3
                   grind)
                | (have i₁ := b25e19 (M.op X1 X2) X0
                   have i₂ := b25e15 X0 X1 X2 X3
                   grind)
                | exact superpose b25e15 b25e19
                | (have j0 := b25e19 (M.op X1 X3) X0
                   grind)
                | (have r₁ := b25e19 X0 (M.op X0 (M.op X0 X2))
                   have r₂ := b25e15 X0 X0 X2 (M.op X0 X2)
                   grind)
                | exact resolve b25e19 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e70 : x = y ∨ y = (k y x) := by grind
              clear b25e66
              have b25e71 : y = (k y x) := by
                first
                | (have r₁ := b25e70
                   have r₂ := b25e27
                   grind)
                | exact resolve b25e70 b25e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e70
              have b25e74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e81 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X1 X0 X2 x
                   have i₂ := b25e54 X0
                   grind)
                | (have i₁ := b25e15 X0 x X2 X0
                   have i₂ := b25e54 X0
                   grind)
                | exact superpose b25e54 b25e15
                | exact resolve b25e15 b25e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e82 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (M.op X1 (M.op x X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X1 X0 x X2
                   have i₂ := b25e54 X0
                   grind)
                | (have i₁ := b25e15 X0 x X0 x
                   have i₂ := b25e54 X0
                   grind)
                | exact superpose b25e54 b25e15
                | exact resolve b25e15 b25e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e92 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op (M.op X0 X2) X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e82 X0 X1 X2
                   have i₂ := b25e49 X1 X0
                   grind)
                | exact superpose b25e49 b25e82
                | exact resolve b25e82 b25e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e82
              have b25e93 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e81 X0 X1 X2
                   have i₂ := b25e44 X1 X0
                   grind)
                | exact superpose b25e44 b25e81
                | exact resolve b25e81 b25e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44 b25e81
              have b25e127 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e21 X2 (k X0 (τ X1))
                   have i₂ := b25e32 X1 X0
                   grind)
                | exact superpose b25e32 b25e21
                | exact resolve b25e21 b25e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e32
              have b25e395 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op x X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e52 X1 X0 X2 x
                   have i₂ := b25e54 X0
                   grind)
                | (have i₁ := b25e52 X0 x X2 X0
                   have i₂ := b25e54 X0
                   grind)
                | exact superpose b25e54 b25e52
                | exact resolve b25e52 b25e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e52
              have b25e468 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op X1 (M.op X0 X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e395 X0 X1 X2
                   have i₂ := b25e49 X1 X0
                   grind)
                | exact superpose b25e49 b25e395
                | exact resolve b25e395 b25e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e49 b25e395
              have b25e3606 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e35 (M.op (τ X0) (τ X0))
                   have i₂ := b25e43 X0
                   grind)
                | exact superpose b25e43 b25e35
                | exact resolve b25e35 b25e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e43
              have b25e3612 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) x) := by
                intro X0
                first
                | (have i₁ := b25e3606 X0
                   have i₂ := b25e93 X0 (M.op X0 X0) X0
                   grind)
                | exact superpose b25e93 b25e3606
                | exact resolve b25e3606 b25e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3606
              have b25e3614 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op x (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e3612 X0
                   have i₂ := b25e54 (M.op X0 X0)
                   grind)
                | exact superpose b25e54 b25e3612
                | exact resolve b25e3612 b25e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3612
              have b25e3615 : ∀ X0 : G, (M.op x x) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
                intro X0
                first
                | (have i₁ := b25e3614 X0
                   have i₂ := b25e93 X0 x X0
                   grind)
                | exact superpose b25e93 b25e3614
                | exact resolve b25e3614 b25e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3614
              have b25e3616 : ∀ X0 : G, (M.op x x) = (σ (M.op (M.op (τ X0) (τ X0)) x)) := by
                intro X0
                first
                | (have i₁ := b25e3615 X0
                   have i₂ := b25e93 (τ X0) (M.op (τ X0) (τ X0)) (τ X0)
                   grind)
                | exact superpose b25e93 b25e3615
                | exact resolve b25e3615 b25e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3615
              have b25e3617 : ∀ X0 : G, (M.op x x) = (σ (M.op x (M.op (τ X0) (τ X0)))) := by
                intro X0
                first
                | (have i₁ := b25e3616 X0
                   have i₂ := b25e54 (M.op (τ X0) (τ X0))
                   grind)
                | exact superpose b25e54 b25e3616
                | exact resolve b25e3616 b25e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3616
              have b25e3618 : (M.op x x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b25e3617 x
                   have i₂ := b25e93 (τ x) x (τ x)
                   grind)
                | exact superpose b25e93 b25e3617
                | exact resolve b25e3617 b25e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3617
              have b25e3834 : (M.op x x) = (τ (M.op x x)) := by
                first
                | (have i₁ := b25e16 (M.op x x)
                   have i₂ := b25e3618
                   grind)
                | exact superpose b25e3618 b25e16
                | exact resolve b25e16 b25e3618
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3618
              have b25e3869 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) X3) ≠ (M.op X2 (σ (k X0 X1))) ∨ (M.op (σ X1) X3) = X2 ∨ (k X2 (M.op (σ X1) X3)) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e68 X2 (σ X1) (σ X0) X3
                   have i₂ := b25e74 X1 X0
                   grind)
                | exact superpose b25e74 b25e68
                | (have j0 := b25e68 X2 (σ X1) X2 X3
                   have j1 := b25e74 X1 X0
                   grind)
                | exact resolve b25e68 b25e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e68
              have b25e6518 : ∀ X0 X1 X2 : G, (σ (k X2 (k X1 (τ X0)))) = (k (σ X2) (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e127 X1 X0 X2
                   have i₂ := b25e20 (σ X1) X0
                   grind)
                | exact superpose b25e20 b25e127
                | (have j1 := b25e20 (σ X1) X0
                   grind)
                | exact resolve b25e127 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e127
              have b25e15308 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op X1 (σ y)) ∨ (M.op (σ x) X0) = X1 ∨ (k X1 (M.op (σ x) X0)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                intro X0 X1
                first
                | (have i₁ := b25e3869 y x X1 X0
                   have i₂ := b25e71
                   grind)
                | exact superpose b25e71 b25e3869
                | (have j0 := b25e3869 y x X1 X0
                   grind)
                | exact resolve b25e3869 b25e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e15343 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (σ X0) (σ (k X1 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ (k X1 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have j0 := b25e3869 X1 X0 (σ X0) (σ (k X1 X0))
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3869
              have b25e15366 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op X1 (σ y)) ∨ (M.op (σ x) X0) = X1 ∨ (k X1 (M.op (σ x) X0)) = X1 ∨ (σ x) = (σ y) := by
                intro X0 X1
                first
                | (have j0 := b25e15308 X0 X1
                   grind)
                | (have r₁ := b25e15308 (σ y) (σ x)
                   have r₂ := b25e30
                   grind)
                | (have r₁ := b25e15308 X0 X1
                   have r₂ := b25e30
                   grind)
                | exact resolve b25e15308 b25e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e15308
              have b25e15397 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op X1 (σ y)) ∨ (M.op (σ x) X0) = X1 ∨ (k X1 (M.op (σ x) X0)) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e15366 X0 X1
                   grind)
                | (have r₁ := b25e15366 X0 X1
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e15366 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e15366
              have b25e35831 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
                first
                | (have j0 := b25e15397 (σ y) (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e15397
              have b25e35832 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
                first
                | (have r₁ := b25e35831
                   have r₂ := b25e30
                   grind)
                | exact resolve b25e35831 b25e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35831
              have b25e35887 : (σ x) = (k (σ x) (σ (k y x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e35832
                   have i₂ := b25e74 x y
                   grind)
                | exact superpose b25e74 b25e35832
                | (have j1 := b25e74 x y
                   grind)
                | exact resolve b25e35832 b25e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e35895 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e20 (σ x) (M.op (σ x) (σ y))
                   have i₂ := b25e35832
                   grind)
                | exact superpose b25e35832 b25e20
                | (have j0 := b25e20 (σ x) (M.op (σ x) (σ y))
                   grind)
                | exact resolve b25e20 b25e35832
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35832
              have b25e35903 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
                first
                | (have r₁ := b25e35895
                   have r₂ := b25e30
                   grind)
                | exact resolve b25e35895 b25e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35895
              have b25e35910 : (σ x) = (k (σ x) (σ (k y x))) ∨ (σ x) = (σ y) := by
                first
                | (have r₁ := b25e35887
                   have r₂ := b25e30
                   grind)
                | exact resolve b25e35887 b25e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35887
              have b25e35912 : (σ x) = (M.op x (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
                first
                | (have i₁ := b25e35903
                   have i₂ := b25e92 (σ x) (σ x) (σ y)
                   grind)
                | exact superpose b25e92 b25e35903
                | exact resolve b25e35903 b25e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35903
              have b25e35914 : (σ x) = (k (σ x) (σ (k y x))) := by
                first
                | (have r₁ := b25e35910
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e35910 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35910
              have b25e35916 : (M.op (σ x) (σ y)) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) := by
                first
                | (have i₁ := b25e35912
                   have i₂ := b25e92 (σ x) (σ x) (σ y)
                   grind)
                | exact superpose b25e92 b25e35912
                | exact resolve b25e35912 b25e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35912
              have b25e35918 : (σ x) = (σ (k x (k y x))) := by
                first
                | (have i₁ := b25e35914
                   have i₂ := b25e21 x (k y x)
                   grind)
                | exact superpose b25e21 b25e35914
                | exact resolve b25e35914 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35914
              have b25e35919 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b25e35918
                   have i₂ := b25e71
                   grind)
                | exact superpose b25e71 b25e35918
                | exact resolve b25e35918 b25e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35918
              have b25e53089 : (σ (k y x)) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op x (σ x)) := by
                first
                | (have i₁ := b25e74 x y
                   have i₂ := b25e35916
                   grind)
                | exact superpose b25e35916 b25e74
                | (have j0 := b25e74 x y
                   grind)
                | exact resolve b25e74 b25e35916
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e74 b25e35916
              have b25e53134 : (σ (k y x)) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) ∨ (σ x) = (σ y) := by grind
              clear b25e53089
              have b25e53158 : (σ (k y x)) = (M.op x (σ x)) ∨ (σ x) = (M.op x (σ x)) := by
                first
                | (have r₁ := b25e53134
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e53134 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e53134
              have b25e53170 : (σ x) = (M.op x (σ x)) ∨ (σ y) = (M.op x (σ x)) := by
                first
                | (have i₁ := b25e53158
                   have i₂ := b25e71
                   grind)
                | exact superpose b25e71 b25e53158
                | exact resolve b25e53158 b25e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e53158
              have b25e53503 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op x (σ x)) := by
                intro X0
                first
                | (have i₁ := b25e93 x X0 (σ x)
                   have i₂ := b25e53170
                   grind)
                | exact superpose b25e53170 b25e93
                | exact resolve b25e93 b25e53170
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e57814 : (σ x) = (M.op x x) ∨ (σ y) = (M.op x x) ∨ (σ y) = (M.op x (σ x)) := by
                first
                | (have i₁ := b25e53170
                   have i₂ := b25e53503 x
                   grind)
                | exact superpose b25e53503 b25e53170
                | exact resolve b25e53170 b25e53503
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e53170
              have b25e57885 : (σ y) ≠ (M.op x x) ∨ (σ y) = (M.op x (σ x)) := by grind
              clear b25e53503
              have b25e57923 : (σ y) = (M.op x (σ x)) ∨ (σ x) = (M.op x x) := by
                first
                | (have r₁ := b25e57814
                   have r₂ := b25e57885
                   grind)
                | exact resolve b25e57814 b25e57885
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e57814 b25e57885
              have b25e58748 : ∀ X0 : G, (M.op x X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b25e92 x X0 (σ x)
                   have i₂ := b25e57923
                   grind)
                | exact superpose b25e57923 b25e92
                | exact resolve b25e92 b25e57923
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e92
              have b25e60687 : (σ y) ≠ (M.op x (σ x)) ∨ (σ x) = (M.op x x) := by
                first
                | (have i₁ := b25e26
                   have i₂ := b25e58748 (σ x)
                   grind)
                | exact superpose b25e58748 b25e26
                | exact resolve b25e26 b25e58748
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e58748
              have b25e60927 : (σ x) = (M.op x x) := by
                first
                | (have r₁ := b25e60687
                   have r₂ := b25e57923
                   grind)
                | exact resolve b25e60687 b25e57923
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e57923 b25e60687
              have b25e61473 : (σ x) = (τ (σ x)) := by
                first
                | (have i₁ := b25e3834
                   have i₂ := b25e60927
                   grind)
                | exact superpose b25e60927 b25e3834
                | exact resolve b25e3834 b25e60927
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e3834
              have b25e61604 : ∀ X0 : G, (M.op x X0) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b25e468 x X0 x
                   have i₂ := b25e60927
                   grind)
                | exact superpose b25e60927 b25e468
                | exact resolve b25e468 b25e60927
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e468
              have b25e61666 : x = (σ x) := by
                first
                | (have i₁ := b25e61473
                   have i₂ := b25e16 x
                   grind)
                | exact superpose b25e16 b25e61473
                | exact resolve b25e61473 b25e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e61473
              have b25e62127 : x ≠ (σ y) := by
                first
                | (have i₁ := b25e25
                   have i₂ := b25e61666
                   grind)
                | exact superpose b25e61666 b25e25
                | exact resolve b25e25 b25e61666
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e62129 : x ≠ (M.op x (σ y)) := by
                first
                | (have i₁ := b25e30
                   have i₂ := b25e61666
                   grind)
                | exact superpose b25e61666 b25e30
                | exact resolve b25e30 b25e61666
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e30
              have b25e62141 : x = (τ x) := by
                first
                | (have i₁ := b25e16 x
                   have i₂ := b25e61666
                   grind)
                | exact superpose b25e61666 b25e16
                | exact resolve b25e16 b25e61666
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e108947 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e15343 y x
                   have i₂ := b25e35919
                   grind)
                | exact superpose b25e35919 b25e15343
                | (have j0 := b25e15343 y x
                   grind)
                | exact resolve b25e15343 b25e35919
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e15343 b25e35919
              have b25e109020 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
              clear b25e108947
              have b25e109098 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) := by
                first
                | (have r₁ := b25e109020
                   have r₂ := b25e26
                   grind)
                | exact resolve b25e109020 b25e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e109020
              have b25e109266 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) := by
                first
                | (have r₁ := b25e109098
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e109098 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e109098
              have b25e109407 : (σ y) = (k (σ y) (M.op x (σ y))) := by
                first
                | (have i₁ := b25e109266
                   have i₂ := b25e61604 (σ y)
                   grind)
                | exact superpose b25e61604 b25e109266
                | exact resolve b25e109266 b25e61604
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e61604 b25e109266
              have b25e110076 : (σ y) = (σ (k y (k y (τ x)))) ∨ x = (M.op x (σ y)) ∨ x = (σ y) := by
                first
                | (have i₁ := b25e6518 x y y
                   have i₂ := b25e109407
                   grind)
                | exact superpose b25e109407 b25e6518
                | (have j0 := b25e6518 x y x
                   grind)
                | exact resolve b25e6518 b25e109407
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6518 b25e109407
              have b25e110115 : (σ y) = (σ (k y (k y (τ x)))) ∨ x = (σ y) := by
                first
                | (have r₁ := b25e110076
                   have r₂ := b25e62129
                   grind)
                | exact resolve b25e110076 b25e62129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e62129 b25e110076
              have b25e110122 : (σ y) = (σ (k y (k y (τ x)))) := by
                first
                | (have r₁ := b25e110115
                   have r₂ := b25e62127
                   grind)
                | exact resolve b25e110115 b25e62127
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e62127 b25e110115
              have b25e110125 : (σ y) = (σ (k y (k y x))) := by
                first
                | (have i₁ := b25e110122
                   have i₂ := b25e62141
                   grind)
                | exact superpose b25e62141 b25e110122
                | exact resolve b25e110122 b25e62141
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e62141 b25e110122
              have b25e110127 : (σ y) = (σ (k y y)) := by
                first
                | (have i₁ := b25e110125
                   have i₂ := b25e71
                   grind)
                | exact superpose b25e71 b25e110125
                | exact resolve b25e110125 b25e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e71 b25e110125
              have b25e110129 : (σ y) = (σ (M.op y y)) := by grind
              clear b25e110127
              have b25e110605 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y y) (M.op y y))) := by
                first
                | (have i₁ := b25e35 (M.op y y)
                   have i₂ := b25e110129
                   grind)
                | exact superpose b25e110129 b25e35
                | exact resolve b25e35 b25e110129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e110710 : (M.op (σ y) (σ y)) = (σ (M.op (M.op y y) x)) := by
                first
                | (have i₁ := b25e110605
                   have i₂ := b25e93 y (M.op y y) y
                   grind)
                | exact superpose b25e93 b25e110605
                | exact resolve b25e110605 b25e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e110605
              have b25e110724 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op y y))) := by
                first
                | (have i₁ := b25e110710
                   have i₂ := b25e54 (M.op y y)
                   grind)
                | exact superpose b25e54 b25e110710
                | exact resolve b25e110710 b25e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e54 b25e110710
              have b25e110733 : (σ (M.op x x)) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b25e110724
                   have i₂ := b25e93 y x y
                   grind)
                | exact superpose b25e93 b25e110724
                | exact resolve b25e110724 b25e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e93 b25e110724
              have b25e110739 : (σ (M.op x x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b25e110733
                   have i₂ := b25e35 y
                   grind)
                | exact superpose b25e35 b25e110733
                | exact resolve b25e110733 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35 b25e110733
              have b25e110745 : (σ y) = (σ (M.op x x)) := by
                first
                | (have i₁ := b25e110739
                   have i₂ := b25e110129
                   grind)
                | exact superpose b25e110129 b25e110739
                | exact resolve b25e110739 b25e110129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e110129 b25e110739
              have b25e110749 : (σ y) = (σ (σ x)) := by
                first
                | (have i₁ := b25e110745
                   have i₂ := b25e60927
                   grind)
                | exact superpose b25e60927 b25e110745
                | exact resolve b25e110745 b25e60927
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e60927 b25e110745
              have b25e110753 : (σ x) = (σ y) := by
                first
                | (have i₁ := b25e110749
                   have i₂ := b25e61666
                   grind)
                | exact superpose b25e61666 b25e110749
                | exact resolve b25e110749 b25e61666
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e61666 b25e110749
              have b25e110754 : False := by grind
              exact b25e110754
            · have b26e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
                intro X0 X1 X2 X3
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e24 : y ≠ (M.op y x) := by grind
              have b26e25 : (σ x) ≠ (σ y) := by grind
              have b26e26 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e27 : x ≠ y := by grind
              have b26e28 : x ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b26e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b26e33
              have b26e43 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
                intro X0 X1 X2 X3 X5
                first
                | (have i₁ := b26e15 X3 X2 (M.op X0 x) X5
                   have i₂ := b26e15 X2 X0 x X1
                   grind)
                | (have i₁ := b26e15 X0 (M.op X1 X3) X0 X3
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e44 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X4) X5) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e15 X3 (M.op X1 X4) X0 X5
                   have i₂ := b26e15 X0 X1 X2 X4
                   grind)
                | (have i₁ := b26e15 X0 X0 (M.op X1 X2) X3
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e45 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
                intro X0 X1 X2 X4
                first
                | (have i₁ := b26e15 X2 X0 x X4
                   have i₂ := b26e15 X2 X0 x X1
                   grind)
                | (have i₁ := b26e15 (M.op X1 x) X1 X2 x
                   have i₂ := b26e15 (M.op X1 X2) X1 X2 x
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e47 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e15 X3 X2 X4 (M.op X0 x)
                   have i₂ := b26e15 X2 X0 x X1
                   grind)
                | (have i₁ := b26e15 X0 (M.op X1 X3) X2 X0
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e49 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X0 X1 X2 x
                   have i₂ := b26e15 X0 X1 X3 x
                   grind)
                | (have i₁ := b26e15 (M.op X1 X2) X1 X2 X3
                   have i₂ := b26e15 (M.op X1 X3) X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e50 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X2 X5)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e15 (M.op X0 X1) X2 X3 X5
                   have i₂ := b26e15 (M.op X2 X5) X0 X1 X4
                   grind)
                | (have i₁ := b26e15 X0 X1 X2 X3
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e63 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = X0 ∨ (k X0 (M.op X1 X3)) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e19 X0 (M.op X1 X3)
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | (have i₁ := b26e19 (M.op X1 X2) X0
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e19
                | (have j0 := b26e19 (M.op X1 X3) X0
                   grind)
                | (have r₁ := b26e19 X0 (M.op X0 (M.op X0 X2))
                   have r₂ := b26e15 X0 X0 X2 (M.op X0 X2)
                   grind)
                | exact resolve b26e19 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e140 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X2 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e49 X3 X2 X4 (M.op X0 x)
                   have i₂ := b26e15 X2 X0 x X1
                   grind)
                | (have i₁ := b26e49 X0 (M.op X1 X3) X2 X0
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e49
                | exact resolve b26e49 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e245 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (M.op X3 X4) X5)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e49 X2 (M.op X3 X4) X0 X5
                   have i₂ := b26e43 X3 X4 X0 X2 X1
                   grind)
                | (have i₁ := b26e49 (M.op X2 X5) X1 X2 X3
                   have i₂ := b26e43 X0 X1 X2 (M.op X1 X2) X5
                   grind)
                | exact superpose b26e43 b26e49
                | exact resolve b26e49 b26e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e491 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X5 (M.op X0 X6)) (M.op X3 X7)) := by
                intro X0 X1 X2 X3 X4 X5 X6 X7
                first
                | (have i₁ := b26e15 (M.op X5 (M.op X0 X6)) X3 X7 X4
                   have i₂ := b26e44 X5 X0 X6 (M.op X3 X4) X1 X2
                   grind)
                | (have i₁ := b26e15 X3 (M.op X1 X4) X2 X5
                   have i₂ := b26e44 X0 X1 X2 X3 X4 X5
                   grind)
                | exact superpose b26e44 b26e15
                | exact resolve b26e15 b26e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44
              have b26e1085 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X3) X4)) = (M.op (M.op X5 X6) (M.op X0 X7)) := by
                intro X0 X1 X2 X3 X4 X5 X6 X7
                first
                | (have i₁ := b26e43 X2 X3 X5 (M.op X0 X7) X6
                   have i₂ := b26e50 X0 X7 (M.op X2 X3) X5 X1 X4
                   grind)
                | (have i₁ := b26e43 X2 X3 X5 (M.op X0 X7) X6
                   have i₂ := b26e50 X0 X1 (M.op X2 X3) X4 X7 X5
                   grind)
                | exact superpose b26e50 b26e43
                | exact resolve b26e43 b26e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e50
              have b26e1592 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 (M.op X0 X1)) = X0 := by
                intro X0 X1
                first
                | (have j0 := b26e63 X0 X0 x (M.op X0 X1)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e63
              have b26e1857 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e71 x y
                   grind)
                | exact superpose b26e71 b26e22
                | (have j1 := b26e71 x y
                   grind)
                | exact resolve b26e22 b26e71
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e71
              have b26e1893 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e1857
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e1857 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1857
              have b26e2330 : ∀ X0 X1 X2 X5 X6 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X5 X6)) := by
                intro X0 X1 X2 X5 X6
                first
                | (have i₁ := b26e140 x x X5 X2 X6
                   have i₂ := b26e245 X0 X1 X2 x x X5
                   grind)
                | (have i₁ := b26e140 X0 X1 X2 (M.op X0 X1) x
                   have i₂ := b26e245 X0 X1 (M.op (M.op X0 X1) X2) x x X5
                   grind)
                | exact superpose b26e245 b26e140
                | exact resolve b26e140 b26e245
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e140
              have b26e2332 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e43 x x X0 X2 X1
                   have i₂ := b26e245 X3 X4 X2 x x X0
                   grind)
                | (have i₁ := b26e43 X0 X1 X2 (M.op X0 X1) x
                   have i₂ := b26e245 X0 X1 (M.op (M.op X0 X1) X2) X3 X4 x
                   grind)
                | exact superpose b26e245 b26e43
                | exact resolve b26e43 b26e245
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e43 b26e245
              have b26e2546 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e47 x x X1 X0 X2
                   have i₂ := b26e2330 (M.op x x) X1 X0 X3 X4
                   grind)
                | (have i₁ := b26e47 X0 X1 X2 (M.op x x) X4
                   have i₂ := b26e2330 X0 X1 (M.op (M.op X0 X1) X2) x x
                   grind)
                | exact superpose b26e2330 b26e47
                | exact resolve b26e47 b26e2330
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e47 b26e2330
              have b26e60143 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b26e1893
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e1893
                | (have j1 := b26e20 y x
                   grind)
                | (have r₁ := b26e1893
                   have r₂ := b26e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b26e1893
                   have r₂ := b26e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b26e1893 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1893
              have b26e60144 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
              clear b26e60143
              have b26e60145 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
                first
                | (have r₁ := b26e60144
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e60144 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60144
              have b26e60146 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e60145
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e60145 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60145
              have b26e60156 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b26e19 (σ y) (σ x)
                   have i₂ := b26e60146
                   grind)
                | exact superpose b26e60146 b26e19
                | (have j0 := b26e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b26e19 (σ y) (σ x)
                   have r₂ := b26e60146
                   grind)
                | exact resolve b26e19 b26e60146
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e60252 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ x) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e2332 X0 X1 X2 (σ x) (σ y)
                   have i₂ := b26e60146
                   grind)
                | exact superpose b26e60146 b26e2332
                | exact resolve b26e2332 b26e60146
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e60258 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ x)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e2546 X0 X1 X2 (σ x) (σ y)
                   have i₂ := b26e60146
                   grind)
                | exact superpose b26e60146 b26e2546
                | exact resolve b26e2546 b26e60146
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60146
              have b26e60267 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
              clear b26e60156
              have b26e60295 : (σ y) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b26e60267
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e60267 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60267
              have b26e60317 : (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e60295
                   have i₂ := b26e21 y x
                   grind)
                | exact superpose b26e21 b26e60295
                | exact resolve b26e60295 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60295
              have b26e64295 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b26e60317
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e60317
                | (have j1 := b26e20 y x
                   grind)
                | exact resolve b26e60317 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e64297 : (k y x) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (k y x)
                   have i₂ := b26e60317
                   grind)
                | exact superpose b26e60317 b26e16
                | exact resolve b26e16 b26e60317
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60317
              have b26e64333 : y = (k y x) := by
                first
                | (have i₁ := b26e64297
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e64297
                | exact resolve b26e64297 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64297
              have b26e64334 : (σ (M.op x y)) = (σ y) ∨ x = y := by
                first
                | (have r₁ := b26e64295
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e64295 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64295
              have b26e64335 : (σ (M.op x y)) = (σ y) := by
                first
                | (have r₁ := b26e64334
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e64334 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64334
              have b26e66322 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
                first
                | (have i₁ := b26e20 y x
                   have i₂ := b26e64333
                   grind)
                | exact superpose b26e64333 b26e20
                | (have j0 := b26e20 y x
                   grind)
                | exact resolve b26e20 b26e64333
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64333
              have b26e66323 : y = (M.op x y) ∨ x = y := by
                first
                | (have r₁ := b26e66322
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e66322 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e66322
              have b26e66325 : y = (M.op x y) := by
                first
                | (have r₁ := b26e66323
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e66323 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e66323
              have b26e68448 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e1592 x y
                   have i₂ := b26e66325
                   grind)
                | exact superpose b26e66325 b26e1592
                | exact resolve b26e1592 b26e66325
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1592
              have b26e68453 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e2332 X0 X1 X2 x y
                   have i₂ := b26e66325
                   grind)
                | exact superpose b26e66325 b26e2332
                | exact resolve b26e2332 b26e66325
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e68455 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e2546 X0 X1 X2 x y
                   have i₂ := b26e66325
                   grind)
                | exact superpose b26e66325 b26e2546
                | exact resolve b26e2546 b26e66325
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e68456 : x = (k x (M.op x y)) := by
                first
                | (have r₁ := b26e68448
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e68448 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68448
              have b26e68491 : x = (k x y) := by
                first
                | (have i₁ := b26e68456
                   have i₂ := b26e66325
                   grind)
                | exact superpose b26e66325 b26e68456
                | exact resolve b26e68456 b26e66325
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68456
              have b26e70601 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
                first
                | (have i₁ := b26e20 x y
                   have i₂ := b26e68491
                   grind)
                | exact superpose b26e68491 b26e20
                | (have j0 := b26e20 x y
                   grind)
                | exact resolve b26e20 b26e68491
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68491
              have b26e70602 : x = (M.op y x) ∨ x = y := by
                first
                | (have r₁ := b26e70601
                   have r₂ := b26e24
                   grind)
                | exact resolve b26e70601 b26e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70601
              have b26e70604 : x = (M.op y x) := by
                first
                | (have r₁ := b26e70602
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e70602 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70602
              have b26e72702 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op y X0) X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e45 y X0 X1 x
                   have i₂ := b26e70604
                   grind)
                | exact superpose b26e70604 b26e45
                | exact resolve b26e45 b26e70604
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e45
              have b26e72707 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 x) := by
                intro X0 X1
                first
                | (have i₁ := b26e49 X0 y X1 x
                   have i₂ := b26e70604
                   grind)
                | exact superpose b26e70604 b26e49
                | exact resolve b26e49 b26e70604
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e49
              have b26e72782 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) x) = (M.op (M.op X3 (M.op X0 X4)) (M.op y X5)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e491 X0 X1 X2 y x X3 X4 X5
                   have i₂ := b26e70604
                   grind)
                | exact superpose b26e70604 b26e491
                | exact resolve b26e491 b26e70604
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e491
              have b26e72801 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op x (M.op (M.op X0 X1) X2)) = (M.op (M.op X3 X4) (M.op y X5)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b26e1085 y x X0 X1 X2 X3 X4 X5
                   have i₂ := b26e70604
                   grind)
                | exact superpose b26e70604 b26e1085
                | exact resolve b26e1085 b26e70604
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1085
              have b26e72811 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e2332 X0 X1 X2 y x
                   have i₂ := b26e70604
                   grind)
                | exact superpose b26e70604 b26e2332
                | exact resolve b26e2332 b26e70604
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2332
              have b26e72813 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 x) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e2546 X0 X1 X2 y x
                   have i₂ := b26e70604
                   grind)
                | exact superpose b26e70604 b26e2546
                | exact resolve b26e2546 b26e70604
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2546 b26e70604
              have b26e72814 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b26e72813 X0 x x
                   have i₂ := b26e68455 X0 x x
                   grind)
                | exact superpose b26e68455 b26e72813
                | exact resolve b26e72813 b26e68455
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68455 b26e72813
              have b26e72816 : ∀ X2 : G, (M.op x X2) = (M.op y X2) := by
                intro X2
                first
                | (have i₁ := b26e72811 x x X2
                   have i₂ := b26e68453 x x X2
                   grind)
                | exact superpose b26e68453 b26e72811
                | exact resolve b26e72811 b26e68453
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68453 b26e72811
              have b26e72823 : ∀ X0 X1 X2 X5 : G, (M.op x (M.op (M.op X0 X1) X2)) = (M.op (σ x) (M.op y X5)) := by
                intro X0 X1 X2 X5
                first
                | (have i₁ := b26e72801 X0 X1 X2 x x X5
                   have i₂ := b26e60252 x x (M.op y X5)
                   grind)
                | exact superpose b26e60252 b26e72801
                | exact resolve b26e72801 b26e60252
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72801
              have b26e72832 : ∀ X0 X1 X2 X5 : G, (M.op (M.op (M.op X0 X1) X2) x) = (M.op (σ x) (M.op y X5)) := by
                intro X0 X1 X2 X5
                first
                | (have i₁ := b26e72782 X0 X1 X2 x x X5
                   have i₂ := b26e60252 x (M.op X0 x) (M.op y X5)
                   grind)
                | exact superpose b26e60252 b26e72782
                | exact resolve b26e72782 b26e60252
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72782
              have b26e72859 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b26e72707 X0 x
                   have i₂ := b26e60258 X0 y x
                   grind)
                | exact superpose b26e60258 b26e72707
                | exact resolve b26e72707 b26e60258
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72707
              have b26e72861 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) := by
                intro X1
                first
                | (have i₁ := b26e72702 x X1
                   have i₂ := b26e60252 y x X1
                   grind)
                | exact superpose b26e60252 b26e72702
                | exact resolve b26e72702 b26e60252
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72702
              have b26e72868 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op x (M.op (M.op X0 X1) X2)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e72823 X0 X1 X2 x
                   have i₂ := b26e60258 (σ x) y x
                   grind)
                | exact superpose b26e60258 b26e72823
                | exact resolve b26e72823 b26e60258
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72823
              have b26e72877 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op X0 X1) X2) x) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e72832 X0 X1 X2 x
                   have i₂ := b26e60258 (σ x) y x
                   grind)
                | exact superpose b26e60258 b26e72832
                | exact resolve b26e72832 b26e60258
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72832
              have b26e72904 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e72859 X0
                   have i₂ := b26e72814 X0
                   grind)
                | exact superpose b26e72814 b26e72859
                | exact resolve b26e72859 b26e72814
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72859
              have b26e72906 : ∀ X1 : G, (M.op (σ x) X1) = (M.op y X1) := by
                intro X1
                first
                | (have i₁ := b26e72861 X1
                   have i₂ := b26e72816 X1
                   grind)
                | exact superpose b26e72816 b26e72861
                | exact resolve b26e72861 b26e72816
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72816 b26e72861
              have b26e72912 : (M.op (σ x) (σ x)) = (M.op x (σ x)) := by
                first
                | (have i₁ := b26e72868 x x x
                   have i₂ := b26e60258 x (M.op x x) x
                   grind)
                | exact superpose b26e60258 b26e72868
                | exact resolve b26e72868 b26e60258
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60258 b26e72868
              have b26e72921 : (M.op (σ x) (σ x)) = (M.op (σ x) x) := by
                first
                | (have i₁ := b26e72877 x x x
                   have i₂ := b26e60252 (M.op x x) x x
                   grind)
                | exact superpose b26e60252 b26e72877
                | exact resolve b26e72877 b26e60252
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60252 b26e72877
              have b26e72949 : (M.op x y) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b26e72912
                   have i₂ := b26e72904 x
                   grind)
                | exact superpose b26e72904 b26e72912
                | exact resolve b26e72912 b26e72904
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72912
              have b26e72956 : (M.op y x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b26e72921
                   have i₂ := b26e72906 x
                   grind)
                | exact superpose b26e72906 b26e72921
                | exact resolve b26e72921 b26e72906
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72906 b26e72921
              have b26e72968 : (M.op x y) = (σ (M.op x x)) := by
                first
                | (have i₁ := b26e72949
                   have i₂ := b26e34 x
                   grind)
                | exact superpose b26e34 b26e72949
                | exact resolve b26e72949 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72949
              have b26e72975 : (M.op y x) = (σ (M.op x x)) := by
                first
                | (have i₁ := b26e72956
                   have i₂ := b26e34 x
                   grind)
                | exact superpose b26e34 b26e72956
                | exact resolve b26e72956 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34 b26e72956
              have b26e72987 : (M.op x y) = (σ (M.op x y)) := by
                first
                | (have i₁ := b26e72968
                   have i₂ := b26e72814 x
                   grind)
                | exact superpose b26e72814 b26e72968
                | exact resolve b26e72968 b26e72814
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72968
              have b26e72994 : (σ (M.op x y)) = (M.op y x) := by
                first
                | (have i₁ := b26e72975
                   have i₂ := b26e72814 x
                   grind)
                | exact superpose b26e72814 b26e72975
                | exact resolve b26e72975 b26e72814
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72975
              have b26e73005 : (M.op x y) = (σ y) := by
                first
                | (have i₁ := b26e72987
                   have i₂ := b26e64335
                   grind)
                | exact superpose b26e64335 b26e72987
                | exact resolve b26e72987 b26e64335
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72987
              have b26e73008 : (σ (M.op x y)) = (M.op y y) := by
                first
                | (have i₁ := b26e72994
                   have i₂ := b26e72814 y
                   grind)
                | exact superpose b26e72814 b26e72994
                | exact resolve b26e72994 b26e72814
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72814 b26e72994
              have b26e73015 : y = (σ y) := by
                first
                | (have i₁ := b26e73005
                   have i₂ := b26e66325
                   grind)
                | exact superpose b26e66325 b26e73005
                | exact resolve b26e73005 b26e66325
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e66325 b26e73005
              have b26e73018 : (σ y) = (M.op y y) := by
                first
                | (have i₁ := b26e73008
                   have i₂ := b26e64335
                   grind)
                | exact superpose b26e64335 b26e73008
                | exact resolve b26e73008 b26e64335
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e64335 b26e73008
              have b26e73025 : y = (M.op y y) := by
                first
                | (have i₁ := b26e73018
                   have i₂ := b26e73015
                   grind)
                | exact superpose b26e73015 b26e73018
                | exact resolve b26e73018 b26e73015
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73018
              have b26e75164 : y ≠ (M.op y (σ x)) := by
                first
                | (have i₁ := b26e26
                   have i₂ := b26e73015
                   grind)
                | exact superpose b26e73015 b26e26
                | exact resolve b26e26 b26e73015
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e73015
              have b26e75189 : y ≠ (M.op y y) := by
                first
                | (have i₁ := b26e75164
                   have i₂ := b26e72904 y
                   grind)
                | exact superpose b26e72904 b26e75164
                | exact resolve b26e75164 b26e72904
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72904 b26e75164
              have b26e75192 : False := by grind
              exact b26e75192
